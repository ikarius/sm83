const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

const logic = @import("logic.zig");
const setLSB = logic.setLSB;
const setMSB = logic.setMSB;
const LSB = logic.LSB;
const MSB = logic.MSB;
const hc8 = logic.hc8;
const hc16 = logic.hc16;
const toggleBit = logic.toggleBit;

// handling endianness for register pointers
const ENDIAN = @import("builtin").target.cpu.arch.endian();
const msb_index = if (ENDIAN == std.builtin.Endian.little) 1 else 0;
const lsb_index = if (ENDIAN == std.builtin.Endian.little) 0 else 1;

/// Basic structure of a CPU :
///
/// registers + mem + internal switches
/// and some logical functions related to registers logic
pub const SM83 = struct {

    // The SM83 is a simplified Z80, registers will be handled as 16b by default.
    AF: u16 = 0, // Acc + Flags
    BC: u16 = 0,
    DE: u16 = 0,
    HL: u16 = 0,
    SP: u16 = 0, // Stack pointer
    PC: u16 = 0, // Program counter

    // This can only be an *image* of the "real" memory,
    // it is only a flat 64kb not taking ROM or memory mappers into account.
    // Memory is not initialized by default
    mem: [1024 * 64]u8 = undefined,

    // current operation
    curOp: Op = undefined,
    // accumulated t-states
    curTs: u32 = 0,

    // 8 bit registers can't be accessed directly

    pub fn A(self: SM83) u8 {
        return MSB(self.AF);
    }

    pub fn B(self: SM83) u8 {
        return MSB(self.BC);
    }

    pub fn C(self: SM83) u8 {
        return LSB(self.BC);
    }

    pub fn D(self: SM83) u8 {
        return MSB(self.DE);
    }

    pub fn E(self: SM83) u8 {
        return LSB(self.DE);
    }

    pub fn F(self: SM83) u8 {
        return LSB(self.AF);
    }

    pub fn H(self: SM83) u8 {
        return MSB(self.HL);
    }

    pub fn L(self: SM83) u8 {
        return LSB(self.HL);
    }

    /// Reset the CPU : all registers to 0, memory flushed and reset count of t-states.
    pub fn reset(self: *SM83) void {
        self.AF = 0;
        self.BC = 0;
        self.DE = 0;
        self.HL = 0;
        self.SP = 0;
        self.PC = 0;

        for (self.mem) |i| {
            self.mem[i] = 0;
        }

        self.curOp = undefined;
        self.curTs = 0;
    }

    /// Get the immediate 16 bit value after the current instruction.
    pub fn imm16(self: SM83) u16 {
        return @as(u16, self.mem[self.PC +% 2]) << 8 | self.mem[self.PC +% 1];
    }

    /// Get the immediate 8 bit value after the current instruction.
    pub fn imm8(self: SM83) u8 {
        return self.mem[self.PC + 1];
    }

    // 8 bit registers can't be set directly
    // but can be set by "reflection" with `OpTarget`.

    pub fn setR8(self: *SM83, reg: Target, val: u8) void {
        switch (reg) {
            .B => self.BC = setMSB(self.BC, val),
            .C => self.BC = setLSB(self.BC, val),
            .D => self.DE = setMSB(self.DE, val),
            .E => self.DE = setLSB(self.DE, val),
            .H => self.HL = setMSB(self.HL, val),
            .L => self.HL = setLSB(self.HL, val),
            .A => self.AF = setMSB(self.AF, val),
            ._HL_ => self.mem[self.HL] = val,
            else => unreachable,
        }
    }

    pub fn r8(self: SM83, reg: Target) u8 {
        return switch (reg) {
            .A => MSB(self.AF),
            .B => MSB(self.BC),
            .C => LSB(self.BC),
            .D => MSB(self.DE),
            .E => LSB(self.DE),
            .H => MSB(self.HL),
            .L => LSB(self.HL),
            ._HL_ => self.mem[self.HL],
            else => unreachable,
        };
    }

    // 16 bits registers can be accessed directly
    // or by "reflection" with OpTarget

    pub fn r16(self: SM83, reg: Target) u16 {
        return switch (reg) {
            .BC => self.BC,
            .DE => self.DE,
            .HL, .HLd, .HLi => self.HL,
            .SP => self.SP,
            else => unreachable,
        };
    }

    pub fn setR16(self: *SM83, reg: Target, val: u16) void {
        switch (reg) {
            .BC => self.BC = val,
            .DE => self.DE = val,
            .HL => self.HL = val,
            .SP => self.SP = val,
            else => unreachable,
        }
    }

    /// Set a flag on register F.
    fn setFlag(self: *SM83, cf: Flag, val: bool) void {
        // FIXME: twisted
        self.AF = self.AF & 0xff00 | toggleBit(self.F(), @intFromEnum(cf), val);
    }

    fn flag(self: *SM83, f: Flag) bool {
        return switch (f) {
            .Z => self.AF & 0x0080 == 0x80,
            .N => self.AF & 0x0040 == 0x40,
            .H => self.AF & 0x0020 == 0x20,
            .C => self.AF & 0x0010 == 0x10,
        };
    }

    fn cond(self: SM83, c: Cond) bool {
        const f = self.F();
        return switch (c) {
            .NZ => f & 0x80 == 0x0,
            .Z => f & 0x80 == 0x80,
            .NC => f & 0x10 == 0x0,
            .C => f & 0x10 == 0x10,
        };
    }

    /// Return current operation code (byte at address PC).
    fn opCode(self: SM83) u8 {
        return self.mem[self.PC];
    }

    /// Execute an operation.
    pub fn exec(self: *SM83, op: Op) void {
        // exec wraps op execution, PC update and timing calculations
        self.curOp = op;
        op.func(self, op);
        // to be accurate, PC should be incremented *before* op execution
        self.PC +%= op.offset;
        self.curTs += op.tstates;
    }

    /// Execute an operation at a specific address.
    pub fn execAt(self: *SM83, addr: u16) void {
        // TODO: maybe inlining would be a good idea (or not)
        self.exec(decode(self.mem[addr]));
    }
};

test "CPU imm16" {
    var CPU = SM83{};

    CPU.mem[0] = 0x00;
    CPU.mem[1] = 0x34;
    CPU.mem[2] = 0x12;

    try expect(CPU.imm16() == 0x1234);
}

test "CPU imm8" {
    var CPU = SM83{};

    CPU.mem[0] = 0x00;
    CPU.mem[1] = 0x42;

    try expect(CPU.imm8() == 0x42);
}

/// Flags : Z, N, H, C are F register bits.
const Flag = enum(u3) {
    Z = 7, // Zero
    N = 6, // Substraction
    H = 5, // Half-Carry
    C = 4, // Carry
};

const Cond = enum(u2) {
    NZ,
    Z,
    NC,
    C,

    fn forOpcode(opCode: u8) Cond {
        return @enumFromInt((opCode & 0x18) >> 3);
    }
};

// First I would like to test some really basic operations on the CPU
// like load simple registers, but I would like to see if some macros / comptime are possible
// to avoid code duplication

// Experimental (still) :
// CPU operations

/// Operands found in a CPU operation:
///
/// an op can have 0, 1 or 2 operands (`src` and `dest`).
/// - register `BC` (reg16) and `0x1234` (imm16) in op `LD BC,01234H`
/// - register `B` (reg8) and value of `[HL]` (reg16ind) in op `LD B,[HL]`
/// - register 'A' (reg8) in op `INC A`
/// - none in `NOP`
/// - bit 3 (bit) and register `A` (reg8) in op `RES 3,A`
/// - address 8bit index H (ind8) and register `A` in op `LDH[ind8],A`
/// - address 16bit index (ind16) and register `A` in op `LD [ind16],A`
const OperandType = enum {
    none,
    reg8,
    reg16,
    imm8,
    imm16,
    ind8,
    ind16,
    reg16ind,
    addr,
    bit,
};

const Target = enum { none, A, B, C, D, E, H, L, _HL_, AF, BC, DE, HL, SP, HLi, HLd, fC, fZ };

/// A CPU operation has 0, 1 or 2 args:
/// - `none`: no argument. No argument for op is `src` and `dest` equal `none`
/// - `imm8` and `imm16`: immediate following value in memory, 8 or 16 bit wide
/// - `r8` and `r16`: registers of the CPU
/// - `r16stk`: 16 bit register used for a stack operation
/// - `r16mem`: address referenced by a 16 bit register (f.i. [HL])
/// - `bit`: operation on a bit
/// - `flag`: operation using flags (f.i. jump/calls)
const Arg = enum {
    none,
    imm8,
    imm16,
    r8,
    r16,
    r16stk,
    r16mem,
    bit,
    cond,
};

/// An `Op` object is the minimal representation of a CPU operation:
/// - `name`: useful for a str representation (disassembly)
/// - `func`: action performed
/// - `src` and `dest`: 0, 1, or 2 `Arg` objects as op arguments
/// - `offset`: PC increment after op
/// - `tstates`: duration in ticks (not cycles)
const Op = struct {
    str: []const u8,
    dest: Arg,
    src: Arg,
    offset: u2,
    tstates: u5,
    func: *const fn (*SM83, Op) void,
};

fn _r8Dest(opCode: u8) Target {
    return switch ((opCode & 0b00111000) >> 3) {
        0 => .B,
        1 => .C,
        2 => .D,
        3 => .E,
        4 => .H,
        5 => .L,
        6 => ._HL_,
        7 => .A,
        else => unreachable,
    };
}

fn _r8Src(opCode: u8) Target {
    return switch (opCode & 0b00000111) {
        0 => .B,
        1 => .C,
        2 => .D,
        3 => .E,
        4 => .H,
        5 => .L,
        6 => ._HL_,
        7 => .A,
        else => unreachable,
    };
}

fn _r16(opCode: u8) Target {
    return switch ((opCode & 0b00110000) >> 4) {
        0 => .BC,
        1 => .DE,
        2 => .HL,
        3 => .SP,
        else => unreachable,
    };
}

fn _r16stk(opCode: u8) Target {
    return switch (opCode & 0b00111000) {
        0 => .BC,
        1 => .DE,
        2 => .HL,
        3 => .AF,
        else => unreachable,
    };
}

fn _r16mem(opCode: u8) Target {
    return switch ((opCode & 0b00110000) >> 4) {
        0 => .BC,
        1 => .DE,
        2 => .HLi,
        3 => .HLd,
        else => unreachable,
    };
}

fn _target(opCode: u8, arg: Arg, argIsSrc: bool) Target {
    return switch (arg) {
        .r8 => if (argIsSrc) _r8Src(opCode) else _r8Dest(opCode),
        .r16 => _r16(opCode),
        else => unreachable,
    };
}

fn _src(opCode: u8, arg: Arg) Target {
    return _target(opCode, arg, true);
}

fn _dest(opCode: u8, arg: Arg) Target {
    return _target(opCode, arg, false);
}

fn decode(opCode: u8) Op {
    return switch (opCode) {
        // current opcode is [PC]: not necessary to store or pass it around
        0x00 => Op{ .str = "NOP", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = nop },
        0x01, 0x11, 0x21, 0x31 => Op{ .str = "LD", .dest = .r16, .src = .imm16, .offset = 3, .tstates = 12, .func = ld },
        0x02, 0x12, 0x22, 0x32 => Op{ .str = "LD", .dest = .r16mem, .src = .none, .offset = 1, .tstates = 8, .func = ld_a },
        0x03, 0x13, 0x23, 0x33 => Op{ .str = "INC", .dest = .r16, .src = .none, .offset = 1, .tstates = 8, .func = inc16 },
        0x04, 0x14, 0x24, 0x34, 0x0c, 0x1c, 0x2c, 0x3c => Op{ .str = "INC", .dest = .r8, .src = .none, .offset = 1, .tstates = 4, .func = inc8 },
        0x05, 0x15, 0x25, 0x35, 0x0d, 0x1d, 0x2d, 0x3d => Op{ .str = "DEC", .dest = .r8, .src = .none, .offset = 1, .tstates = 4, .func = dec8 },
        0x06, 0x16, 0x26, 0x36, 0x0e, 0x1e, 0x2e, 0x3e => Op{ .str = "LD", .dest = .r8, .src = .imm8, .offset = 2, .tstates = 8, .func = ld },
        0x07 => Op{ .str = "RLCA", .dest = .none, .src = .none, .offset = 1, .tstates = 8, .func = rlc },
        0x08 => Op{ .str = "LD", .dest = .none, .src = .none, .offset = 3, .tstates = 20, .func = ld_imm16_sp },
        0x09, 0x19, 0x29, 0x39 => Op{ .str = "LD", .dest = .r16, .src = .r16, .offset = 1, .tstates = 8, .func = add_hl_r16 },
        0x0a, 0x1a, 0x2a, 0x3a => Op{ .str = "LD A,", .dest = .none, .src = .r16mem, .offset = 1, .tstates = 8, .func = ld_a_r16mem },
        0x0b, 0x1b, 0x2b, 0x3b => Op{ .str = "DEC", .dest = .r16, .src = .none, .offset = 1, .tstates = 8, .func = dec16 },
        0x0f => Op{ .str = "RRCA", .dest = .none, .src = .none, .offset = 1, .tstates = 8, .func = rrc },
        0x10 => Op{ .str = "STOP", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = stop },
        0x17 => Op{ .str = "RLA", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = rl },
        0x18 => Op{ .str = "JR ", .dest = .imm8, .src = .none, .offset = 0, .tstates = 0, .func = jr },
        0x1f => Op{ .str = "RRA", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = rr },
        0x20, 0x30, 0x28, 0x38 => Op{ .str = "JR ", .dest = .cond, .src = .none, .offset = 0, .tstates = 0, .func = jr },
        0x27 => Op{ .str = "DAA", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = daa },
        0x2f => Op{ .str = "CPL", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = cpl },
        0x37 => Op{ .str = "SCF", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = scf },
        0x3f => Op{ .str = "CCF", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = ccf },
        0x40...0x75, 0x77...0x7f => Op{ .str = "LD", .dest = .r8, .src = .r8, .offset = 1, .tstates = 4, .func = ld },
        0x76 => Op{ .str = "HALT", .dest = .none, .src = .none, .offset = 1, .tstates = 1, .func = halt },
        0x80...0x87 => Op{ .str = "ADD A", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = add8 },
        0x88...0x8f => Op{ .str = "ADC A", .dest = .none, .src = .none, .offset = 1, .tstates = 4, .func = adc8 },
        // ...
        else => unreachable,
    };
}

// CPU instructions implementation

fn nop(_: *SM83, _: Op) void {}

fn stop(_: *SM83, _: Op) void {
    // FIXME: must find some documentation on what to do with this
}

fn ld_a(cpu: *SM83, _: Op) void {
    // special load case : LD [r16mem],A
    // src does not conform to any mapping, it must be treated as a distinct op
    // (or with an ugly hack)
    const opCode = cpu.mem[cpu.PC];
    const reg = _r16mem(opCode);
    cpu.mem[cpu.r16(reg)] = cpu.A();
    // TODO: check if pull-up relevant
    switch (reg) {
        // [HL+]/[HL-] post-process
        .HLi => cpu.HL += 1,
        .HLd => cpu.HL -= 1,
        else => {},
    }
}

fn ld(cpu: *SM83, op: Op) void {
    const opCode = cpu.mem[cpu.PC];
    switch (op.src) {
        .imm8 => {
            // LD r8,imm8
            cpu.setR8(_dest(opCode, op.dest), cpu.imm8());
        },
        .imm16 => {
            // LD r16, imm16
            cpu.setR16(_dest(opCode, op.dest), cpu.imm16());
        },
        .r8 => {
            switch (op.dest) {
                .r8 => {
                    // LD r8, r8
                    cpu.setR8(_target(opCode, op.dest, false), cpu.r8(_src(opCode, op.src)));
                },
                .r16mem => {
                    // FIXME: LD [r16], r8
                    cpu.mem[cpu.r16(_r16(opCode))] = cpu.r8(_dest(opCode, op.src));
                },
                else => unreachable,
            }
        },
        .r16mem => {
            // only LD A,
        },
        else => unreachable,
    }
}

/// Increments a 16bit register : no flags handling needed.
fn inc16(cpu: *SM83, op: Op) void {
    // doesn't check op validity (in op we trust)
    // handle overflow
    const opCode = cpu.opCode();
    const target = _target(opCode, op.dest, false);

    cpu.setR16(target, cpu.r16(target) +% 1);
}

/// Decrements a 16bit register : no flags handling needed.
fn dec16(cpu: *SM83, _: Op) void {
    // doesn't check op validity (in op we trust)
    // handle overflow
    const opCode = cpu.opCode();
    const target = _r16(opCode);

    cpu.setR16(target, cpu.r16(target) -% 1);
}

/// Increments 8 bit registers, handles flags.
fn inc8(CPU: *SM83, op: Op) void {
    const opCode = CPU.opCode();
    const target = _target(opCode, op.dest, false);

    var value = CPU.r8(target);
    const old = value;
    value +%= 1;

    CPU.setFlag(Flag.H, hc8(old, value, true));
    CPU.setFlag(Flag.Z, value == 0);
    CPU.setFlag(Flag.N, false);
    // C is unchanged

    CPU.setR8(target, value);
}

fn dec8(CPU: *SM83, op: Op) void {
    const opCode = CPU.opCode();
    const target = _target(opCode, op.dest, false);

    var value = CPU.r8(target);
    const old = value;
    value -%= 1;

    CPU.setFlag(Flag.H, hc8(old, value, false));
    CPU.setFlag(Flag.Z, value == 0);
    CPU.setFlag(Flag.N, true);
    // C is unchanged

    CPU.setR8(target, value);
}

fn rlc(cpu: *SM83, op: Op) void {
    // RLC has 2 version RLCA and RLC r8 (with different flag behaviour)
    switch (op.dest) {
        .none => {
            // RLCA : all flags to 0 except Z
            const carry = cpu.A() & 0x80 == 0x80;
            const r = (cpu.A() << 1) | if (carry) @as(u8, 0x01) else @as(u8, 0x00);
            cpu.setR8(.A, @truncate(r));
            cpu.setFlag(.Z, false);
            cpu.setFlag(.N, false);
            cpu.setFlag(.H, false);
            cpu.setFlag(.C, carry);
        },
        .r8 => {
            // RLC r8 : only C and Z affected
            // // FIXME: test
            const target = _dest(cpu.opCode(), op.dest);
            const reg = cpu.r8(target);
            const carry = reg & 0x80 == 0x80;
            const r = (reg << 1) | if (carry) @as(u8, 0x01) else @as(u8, 0x00);
            cpu.setR8(.A, @truncate(r));
            cpu.setFlag(.N, false);
            cpu.setFlag(.H, false);
            cpu.setFlag(.C, carry);
            cpu.setFlag(.Z, cpu.A() == 0);
        },
        else => unreachable,
    }
}

fn ld_imm16_sp(cpu: *SM83, _: Op) void {
    const addr = cpu.imm16();
    cpu.mem[addr] = LSB(cpu.SP);
    cpu.mem[addr + 1] = MSB(cpu.SP);
}

fn add_hl_r16(cpu: *SM83, _: Op) void {
    const src = cpu.r16(_r16(cpu.opCode()));
    var result: u17 = @as(u17, cpu.HL);
    const old = cpu.HL;

    result += src;
    cpu.HL = @truncate(result);

    cpu.setFlag(.H, hc16(old, cpu.HL, true));
    cpu.setFlag(.C, (result >> 16) > 0);
    cpu.setFlag(.N, false);
}

fn ld_a_r16mem(cpu: *SM83, _: Op) void {
    const reg = _r16mem(cpu.opCode());
    cpu.setR8(.A, cpu.mem[cpu.r16(reg)]);
    switch (reg) {
        .HLi => cpu.HL += 1,
        .HLd => cpu.HL -= 1,
        else => {},
    }
}

fn rrc(cpu: *SM83, op: Op) void {
    // RRC has 2 version RLCA and RLC r8 (with different flag behaviour)
    switch (op.dest) {
        .none => {
            // RRCA : all flags to 0 except Z
            const a = cpu.A();
            const carry = (a & 0x01) > 0;
            // note: try to remove the `@as()` and see what happen
            // hint: there is a mix of runtime and comptime values
            const r = (a >> 1) | (if (carry) @as(u8, 0x80) else @as(u8, 0x00));
            cpu.setR8(.A, r);
            cpu.setFlag(.Z, false);
            cpu.setFlag(.N, false);
            cpu.setFlag(.H, false);
            cpu.setFlag(.C, carry);
        },
        .r8 => {
            // RRC r8 : only C and Z affected
            const target = _dest(cpu.opCode(), op.dest);
            const reg = cpu.r8(target);
            const carry = (reg & 0x01) > 0;
            const r = (reg >> 1) | (if (carry) @as(u8, 0x80) else @as(u8, 0x00));
            cpu.setR8(target, r);
            cpu.setFlag(.N, false);
            cpu.setFlag(.H, false);
            cpu.setFlag(.C, carry);
            cpu.setFlag(.Z, reg == 0);
        },
        else => unreachable,
    }
}

fn rl(cpu: *SM83, op: Op) void {
    const reg = switch (op.dest) {
        .none => .A, // RLA
        .r8 => _dest(cpu.opCode(), op.dest), // RL r8
        else => unreachable,
    };
    const val = cpu.r8(reg);
    const carry = cpu.flag(.C);

    cpu.setR8(reg, (val << 1) | (if (carry) @as(u8, 0x01) else @as(u8, 0x00)));

    cpu.setFlag(.N, false);
    cpu.setFlag(.H, false);
    cpu.setFlag(.C, (val & 0x80 == 0x80));
    cpu.setFlag(.Z, if (op.dest == .none) false else cpu.r8(reg) == 0);
}

fn jr(cpu: *SM83, op: Op) void {
    // JR with condition must handle tstates and PC values (depends of condition)
    // duplicate for performance ?
    const offset: i8 = @bitCast(cpu.imm8()); // implicit conversion
    const base: i16 = @bitCast(cpu.PC);
    const jumpto: i16 = base +% offset;
    switch (op.dest) {
        .imm8 => {
            cpu.PC = @bitCast(jumpto);
            cpu.curTs += 12;
        },
        .cond => {
            if (cpu.cond(Cond.forOpcode(cpu.opCode()))) {
                cpu.PC = @bitCast(jumpto);
                cpu.curTs += 12;
            } else {
                cpu.curTs += 8;
            }
        },
        else => unreachable,
    }
    cpu.PC +%= 2;
}

fn rr(cpu: *SM83, op: Op) void {
    const reg = switch (op.dest) {
        .none => .A, // RLA
        .r8 => _dest(cpu.opCode(), op.dest), // RL r8
        else => unreachable,
    };
    const val = cpu.r8(reg);
    const carry = cpu.flag(.C);

    cpu.setR8(reg, (val >> 1) | (if (carry) @as(u8, 0x80) else @as(u8, 0x00)));

    cpu.setFlag(.N, false);
    cpu.setFlag(.H, false);
    cpu.setFlag(.C, (val & 0x01 == 0x01));
    cpu.setFlag(.Z, if (op.dest == .none) false else cpu.r8(reg) == 0);
}

fn daa(cpu: *SM83, _: Op) void {
    //  details about DAA on SM83 here: https://blog.ollien.com/posts/gb-daa/
    var bcd: u8 = 0;
    const a: u8 = cpu.A();
    const add = !cpu.flag(.N);
    var carry = false;

    if ((add and (a & 0xf) > 0x09) or cpu.flag(.H)) {
        bcd |= 0x06;
    }

    if ((add and a > 0x99) or cpu.flag(.C)) {
        bcd |= 0x60;
        carry = true;
    }

    cpu.setR8(.A, if (add) (a +% bcd) else (a -% bcd));
    cpu.setFlag(.H, false);
    cpu.setFlag(.Z, cpu.A() == 0);
    cpu.setFlag(.C, carry);
}

fn cpl(cpu: *SM83, _: Op) void {
    cpu.setR8(.A, ~cpu.A());
    cpu.setFlag(.N, true);
    cpu.setFlag(.H, true);
}

fn scf(cpu: *SM83, _: Op) void {
    cpu.setFlag(.C, true);
    cpu.setFlag(.N, false);
    cpu.setFlag(.H, false);
}

fn ccf(cpu: *SM83, _: Op) void {
    cpu.setFlag(.C, !cpu.flag(.C));
    cpu.setFlag(.N, false);
    cpu.setFlag(.H, false);
}

fn halt(_: *SM83, _: Op) void {
    // FIMXE : implement (last)
}

/// This special 8 bits half-carry/borrow take 3 arguments for operations like `ADC` and `SUBC`.
/// For addition / substraction with 2 arguments, use `logic.hc8`.
fn _hc8(a: u8, b: u8, c: u8, addition: bool) bool {
    return switch (addition) {
        true => ((a & 0x0F) + (b & 0x0F)) + (c & 0x0f) > 0x0f,
        false => (a & 0x0F) < (b & 0x0F),
    };
}

fn _add(cpu: *SM83, carry: bool) void {
    // Only A is used as dest
    const olda = cpu.A();
    const src = _r8Src(cpu.opCode());
    const c = if (cpu.flag(.C) and carry) @as(u8, 0x01) else @as(u8, 0x00);
    const val = cpu.r8(src);

    const result: u9 = @as(u9, olda) + @as(u9, val) + @as(u9, c);

    cpu.setR8(.A, @truncate(result));

    const a = cpu.A();
    cpu.setFlag(.Z, a == 0);
    cpu.setFlag(.N, false);
    // FIXME: this is weird, and will have to check it out (add/sub with 3 terms)
    cpu.setFlag(.H, _hc8(olda, val, c, true));
    cpu.setFlag(.C, result & 0x100 == 0x100);
}

fn add8(cpu: *SM83, _: Op) void {
    _add(cpu, false);
}

fn adc8(cpu: *SM83, _: Op) void {
    _add(cpu, true);
}
