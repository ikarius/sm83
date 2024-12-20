const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

// handling endianness for register pointers
const ENDIAN = @import("builtin").target.cpu.arch.endian();
const msb_index = if (ENDIAN == std.builtin.Endian.little) 1 else 0;
const lsb_index = if (ENDIAN == std.builtin.Endian.little) 0 else 1;

// Basic structure of a CPU : register + mem + internal switches
const SM83 = struct {
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

    fn imm16(self: SM83) u16 {
        return @as(u16, self.mem[self.PC + 2]) << 8 | self.mem[self.PC + 1];
    }

    fn imm8(self: SM83) u8 {
        return self.mem[self.PC + 1];
    }

    // 8 bit registers can't be accessed directly

    fn setR8(self: *SM83, reg: OpTarget, val: u8) void {
        switch (reg) {
            .B => self.BC = setMSB(self.BC, val),
            .C => self.BC = setLSB(self.BC, val),
            .D => self.DE = setMSB(self.DE, val),
            .E => self.DE = setLSB(self.DE, val),
            .H => self.HL = setLSB(self.HL, val),
            .L => self.HL = setMSB(self.HL, val),
            .A => self.AF = setLSB(self.AF, val),
            else => unreachable,
        }
    }

    fn r8(self: SM83, reg: OpTarget) u8 {
        return switch (reg) {
            .A => LSB(self.AF),
            .B => LSB(self.BC),
            .C => MSB(self.BC),
            .D => LSB(self.DE),
            .E => MSB(self.DE),
            .H => LSB(self.HL),
            .L => MSB(self.HL),
            else => unreachable,
        };
    }

    // 16 bits registers can be accessed directly
    // or by "reflection" with OpTarget

    fn r16(self: SM83, reg: OpTarget) u16 {
        return switch (reg) {
            .AF => self.AF, // FIXME: probably useless
            .BC => self.BC,
            .DE => self.DE,
            .HL => self.HL,
            .SP => self.SP,
            else => unreachable,
        };
    }

    fn setR16(self: *SM83, reg: OpTarget, val: u16) void {
        switch (reg) {
            .BC => self.BC = val,
            .DE => self.BC = val,
            .HL => self.BC = val,
            .SP => self.BC = val,
            else => unreachable,
        }
    }
};

test "CPU imm16" {
    cpu.mem[0] = 0x00;
    cpu.mem[1] = 0x34;
    cpu.mem[2] = 0x12;

    try expect(cpu.imm16() == 0x1234);
}

test "CPU imm8" {
    cpu.mem[0] = 0x00;
    cpu.mem[1] = 0x42;

    try expect(cpu.imm8() == 0x42);
}

var cpu = SM83{};

// POC : what I want to do is :
// perform an action (read or write basically) on a given emulated CPU register (Zig type u16 or u8)
// by having only a code representing the register
// for instance : if 0b010 (binary) identifies register DE, I want to be able to read or write a value in DE

const R8imm = enum(u3) {
    // r8 : immediate
    B = 0b000,
    C = 0b001,
    D = 0b010,
    E = 0b011,
    H = 0b100,
    L = 0b101,
    _HL_ = 0b110, // [HL] memory access
    A = 0b111,
};

const R16imm = enum(u2) {
    // r16 : immediate
    BC = 0b00,
    DE = 0b01,
    HL = 0b10,
    SP = 0b11,
};

/// Conditions for the F register of the SM83.
const cond = enum(2) {
    NZ = 0b00, // non-zero
    Z = 0b01, // zero
    NC = 0b10, // non-carry
    C = 0b11, // carry
};

// there is maybe a possibility of using comptime
fn setMSB(reg: u16, val: u8) u16 {
    return (reg & 0x00ff) | @as(u16, val) << 8;
}

fn setLSB(reg: u16, val: u8) u16 {
    return (reg & 0xff00) | val;
}

/// Returns the most significant byte (MSB) of 16 bit register.
fn MSB(reg: u16) u8 {
    return @truncate((reg & 0xff00) >> 8);
}

/// Returns the least significant byte (LSB) of 16 bit register.
fn LSB(reg: u16) u8 {
    return @truncate(reg & 0x00ff);
}

test "MSB/LSB values" {
    const reg = 0x1234;
    try expect(MSB(reg) == 0x12);
    try expect(LSB(reg) == 0x34);
}

// TODO: maybe implement pointer result versions of MSB/LSB.

fn _setR8(code: R8imm, val: u8) void {
    switch (code) {
        R8imm.B => cpu.BC = setMSB(cpu.BC, val),
        R8imm.C => cpu.BC = setLSB(cpu.BC, val),
        R8imm.D => cpu.DE = setMSB(cpu.DE, val),
        R8imm.E => cpu.DE = setLSB(cpu.DE, val),
        R8imm.H => cpu.HL = setMSB(cpu.HL, val),
        R8imm.L => cpu.HL = setMSB(cpu.HL, val),
        R8imm.A => cpu.AF = setMSB(cpu.AF, val),
        R8imm._HL_ => cpu.mem[cpu.HL] = val,
    }
}

fn R8x(code: R8imm) *u8 {
    return switch (code) {
        R8imm.B => &(@as([*]u8, @ptrCast(&cpu.BC))[msb_index]),
        R8imm.C => &(@as([*]u8, @ptrCast(&cpu.BC))[lsb_index]),
        R8imm.D => &(@as([*]u8, @ptrCast(&cpu.DE))[msb_index]),
        R8imm.E => &(@as([*]u8, @ptrCast(&cpu.DE))[lsb_index]),
        R8imm.H => &(@as([*]u8, @ptrCast(&cpu.HL))[msb_index]),
        R8imm.L => &(@as([*]u8, @ptrCast(&cpu.HL))[lsb_index]),
        R8imm.A => &(@as([*]u8, @ptrCast(&cpu.AF))[msb_index]),
        R8imm._HL_ => &cpu.mem[cpu.HL],
    };
}

// First I would like to test some really basic operations on the CPU
// like load simple registers, but I would like to see if some macros / comptime are possible
// to avoid code duplication

test "load (hl)" {
    cpu.HL = 0x1234;
    _setR8(._HL_, 0x13);
    try expect(cpu.mem[cpu.HL] == 0x13);
}

test "access registers via pointers" {
    cpu.DE = 0x1234;
    R8x(.E).* = 0x56;
    try expect(cpu.DE == 0x1256);
}

// Experimental (still) :
// CPU operations

// deprecated
const OpType = enum {
    none,
    reg, // ex. LD A,1 or LD BC,DE (8b or 16b)
    regAddr, // ex. LD (BC),A
    addr, // ex. LD (nn), SP

    fn str(self: OpType) []const u8 {
        return switch (self) {
            .none => "NONE",
            .reg => "REGISTER",
            .regAddr => "INDEXED",
            .addr => "ADDRESS",
        };
    }
};

test "optype str (in enum)" {
    try expect(std.mem.eql(u8, "NONE", OpType.none.str()));
}

/// Operands found in a CPU operation:
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

const OpTarget = enum { none, A, B, C, D, E, H, L, AF, BC, DE, HL, SP, HLI, HLD, _0, _1, _2, _3, _4, _5, _6, _7, IMM8, IMM16 };

/// CPU operations :
/// the structure of a CPU operation (op) is freely inspired from the one of Realboy.
/// - source pair : dest_type, dest
/// - destination pair : src_type, src
const Op = struct {
    code: u8,
    str: []const u8,
    destType: OperandType = .none,
    dest: OpTarget = .none,
    srcType: OperandType = .none,
    src: OpTarget = .none,
    offset: u2,
    tstates: u4,
    func: *const fn (Op) void,
};

fn exec(op: Op) void {
    // exec wraps op execution, PC update and timing calculations
    cpu.curOp = op;
    op.func(op);
    // to be accurate, PC should be incremented *before* op execution
    cpu.PC += op.offset;
    cpu.curTs += op.tstates;
}

fn execAt(addr: u16) void {
    // todo: maybe inlining would be a good idea
    exec(mainOps[cpu.mem[addr]]);
}

const mainOps = [_]Op{
    Op{ .code = 0x00, .str = "NOP", .destType = .none, .dest = .none, .srcType = .none, .src = .none, .offset = 1, .tstates = 4, .func = nop },
    Op{ .code = 0x01, .str = "LD", .destType = .reg16, .dest = .BC, .srcType = .imm16, .src = .none, .offset = 3, .tstates = 12, .func = ld },
    Op{ .code = 0x02, .str = "LD", .destType = .reg16ind, .dest = .BC, .srcType = .reg8, .src = .A, .offset = 1, .tstates = 8, .func = ld },
    Op{ .code = 0x02, .str = "INC", .destType = .reg16, .dest = .BC, .srcType = .none, .src = .none, .offset = 1, .tstates = 8, .func = inc16 },
    // ...
};

fn nop(op: Op) void {
    std.debug.print("op: {s}\n should execute in {d} tstates\n", .{ op.str, op.tstates });
}

test "misc op: NOP" {
    nop(mainOps[0]);
}

fn R16(target: OpTarget) *u16 {
    return switch (target) {
        .AF => &cpu.AF,
        .BC => &cpu.BC,
        .DE => &cpu.DE,
        .HL => &cpu.HL,
        .SP => &cpu.SP,
        else => unreachable,
    };
}

fn R8(target: OpTarget) *u8 {
    return switch (target) {
        .B => &(@as([*]u8, @ptrCast(&cpu.BC))[msb_index]),
        .C => &(@as([*]u8, @ptrCast(&cpu.BC))[lsb_index]),
        .D => &(@as([*]u8, @ptrCast(&cpu.DE))[msb_index]),
        .E => &(@as([*]u8, @ptrCast(&cpu.DE))[lsb_index]),
        .H => &(@as([*]u8, @ptrCast(&cpu.HL))[msb_index]),
        .L => &(@as([*]u8, @ptrCast(&cpu.HL))[lsb_index]),
        .A => &(@as([*]u8, @ptrCast(&cpu.AF))[msb_index]),
        else => unreachable,
    };
}

fn ld(op: Op) void {
    // a beefy one to start with : LD ops are almost half of the operation set
    switch (op.srcType) {
        // process immediate register ops :
        .imm8 => {
            cpu.setR8(op.dest, cpu.imm8());
        },
        .imm16 => {
            // FIXME: no need of pointers here, just set targets
            // R16(op.dest).* = cpu.imm16();
            cpu.setR16(op.dest, cpu.imm16());
        },
        .reg8 => {
            switch (op.destType) {
                .reg8 => {
                    // TODO
                },
                .reg16ind => {
                    cpu.mem[cpu.r16(op.dest)] = cpu.r8(op.src);
                },
                else => unreachable,
            }
        },
        .reg16 => {
            // TODO
        },
        else => unreachable,
    }
}

test "misc op: LD BC,1234H" {
    cpu.mem[0] = 0x01;
    cpu.mem[1] = 0x34;
    cpu.mem[2] = 0x12;
    ld(mainOps[1]);
    try expect(cpu.BC == 0x1234);
}

test "misc op: LD (BC),A" {
    cpu.setR8(.A, 0x42);
    cpu.BC = 0x1234;
    ld(mainOps[2]);

    try expectEqual(0x42, cpu.mem[0x1234]);
}

/// Increments a 16bit register : no flags handling (F)
fn inc16(op: Op) void {
    // doesn't check op validity (in op we trust)
    // handle overflow
    R16(op.dest).* +%= 1;
}

/// Decrements a 16bit register : no flags handling (F)
fn dec16(op: Op) void {
    // doesn't check op validity (in op we trust)
    // handle overflow
    R16(op.dest).* -%= 1;
}

test "misc op: INC BC" {
    cpu.BC = 0x1233;
    exec(mainOps[3]);
    try expect(cpu.BC == 0x1234);

    cpu.BC = 0xFFFF;
    exec(mainOps[3]);
    try expect(cpu.BC == 0x0000);
}

fn inc8() void {}

/// Check if there is a *half-carry* (for addition)
/// or a *half-borrow* (for substraction)
/// performed when moving from `old` value to `new` value.
///
/// The `carry` parameter must be `true` for half-carry check, or `false` for half-borrow.
fn hc8(old: u8, new: u8, carry: bool) bool {
    // Zig idiomatic:
    // maybe be replaced with mask instructions should the need arise (performance)
    return switch (carry) {
        true => @as(u4, @truncate(old)) > @as(u4, @truncate(new)),
        false => @as(u4, @truncate(old)) < @as(u4, @truncate(new)),
    };
}

// TODO: specialized versions (hc, hb ?)

test "half-carry 8b: addition" {
    const old = 0b1111;
    const new = old + 1;

    // no change
    try expect(!hc8(old, old, true));

    // should "carry"
    try expect(hc8(old, new, true));

    const old2 = 0b10111;
    const new2 = old2 + 1;

    // Should not "carry"
    try expect(!hc8(old2, new2, true));
}

test "half-borrow 8b: substraction" {
    const old = 0b10000;
    const new = old - 1;

    // no change
    try expect(!hc8(old, old, false));

    // should "borrow"
    try expect(hc8(old, new, false));

    const old2 = 0b10011;
    const new2 = old2 - 1;

    // Should not "borrow"
    try expect(!hc8(old2, new2, false));
}
