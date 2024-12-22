const std = @import("std");
const expect = std.testing.expect;
const expectEqual = std.testing.expectEqual;

const logic = @import("logic.zig");
const setLSB = logic.setLSB;
const setMSB = logic.setMSB;
const LSB = logic.LSB;
const MSB = logic.MSB;
const hc8 = logic.hc8;

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

    pub fn init(allocator: std.mem.Allocator) !*SM83 {
        const self = try allocator.create(SM83);
        self.reset();
        return self;
    }

    pub fn deinit(self: *SM83, allocator: std.mem.Allocator) void {
        allocator.destroy(self);
    }

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

    pub fn imm16(self: SM83) u16 {
        return @as(u16, self.mem[self.PC + 2]) << 8 | self.mem[self.PC + 1];
    }

    pub fn imm8(self: SM83) u8 {
        return self.mem[self.PC + 1];
    }

    // 8 bit registers can't be accessed directly

    pub fn setR8(self: *SM83, reg: OpTarget, val: u8) void {
        switch (reg) {
            .B => self.BC = setMSB(self.BC, val),
            .C => self.BC = setLSB(self.BC, val),
            .D => self.DE = setMSB(self.DE, val),
            .E => self.DE = setLSB(self.DE, val),
            .H => self.HL = setMSB(self.HL, val),
            .L => self.HL = setLSB(self.HL, val),
            .A => self.AF = setMSB(self.AF, val),
            else => unreachable,
        }
    }

    pub fn r8(self: SM83, reg: OpTarget) u8 {
        return switch (reg) {
            .A => MSB(self.AF),
            .B => MSB(self.BC),
            .C => LSB(self.BC),
            .D => MSB(self.DE),
            .E => LSB(self.DE),
            .H => MSB(self.HL),
            .L => LSB(self.HL),
            else => unreachable,
        };
    }

    // 16 bits registers can be accessed directly
    // or by "reflection" with OpTarget

    pub fn r16(self: SM83, reg: OpTarget) u16 {
        return switch (reg) {
            .AF => self.AF, // FIXME: probably useless
            .BC => self.BC,
            .DE => self.DE,
            .HL => self.HL,
            .SP => self.SP,
            else => unreachable,
        };
    }

    pub fn setR16(self: *SM83, reg: OpTarget, val: u16) void {
        switch (reg) {
            .BC => self.BC = val,
            .DE => self.BC = val,
            .HL => self.BC = val,
            .SP => self.BC = val,
            else => unreachable,
        }
    }

    // fn setF(self:*SM83, cf:flag, val:bool) void {
    //     switch (cf) {
    //         .Z =>
    //     }
    // }
    pub fn exec(self: *SM83, op: Op) void {
        // exec wraps op execution, PC update and timing calculations
        self.curOp = op;
        op.func(self, op);
        // to be accurate, PC should be incremented *before* op execution
        self.PC += op.offset;
        self.curTs += op.tstates;
    }

    pub fn execAt(self: *SM83, addr: u16) void {
        // todo: maybe inlining would be a good idea
        self.exec(mainOps[self.mem[addr]]);
    }
};

test "CPU imm16" {
    var CPU = try SM83.init(std.testing.allocator);
    defer CPU.deinit(std.testing.allocator);

    CPU.mem[0] = 0x00;
    CPU.mem[1] = 0x34;
    CPU.mem[2] = 0x12;

    try expect(CPU.imm16() == 0x1234);
}

test "CPU imm8" {
    var CPU = try SM83.init(std.testing.allocator);
    defer CPU.deinit(std.testing.allocator);

    CPU.mem[0] = 0x00;
    CPU.mem[1] = 0x42;

    try expect(CPU.imm8() == 0x42);
}

// pub var CPU = SM83.init();

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

/// Conditions / flags for the F register of the SM83.
const cond = enum(2) {
    NZ = 0b00, // non-zero
    Z = 0b01, // zero
    NC = 0b10, // non-carry
    C = 0b11, // carry
};

const flag = enum(4) {
    Z = 7,
    N = 6,
    H = 5,
    C = 4,
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

const OpTarget = enum { none, A, B, C, D, E, H, L, AF, BC, DE, HL, SP, HLI, HLD, _0, _1, _2, _3, _4, _5, _6, _7, IMM8, IMM16 };

/// CPU operations :
///
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
    func: *const fn (*SM83, Op) void,
};

/// SM83 operation table
/// a complete list of main operations.
const mainOps = [_]Op{
    Op{ .code = 0x00, .str = "NOP", .destType = .none, .dest = .none, .srcType = .none, .src = .none, .offset = 1, .tstates = 4, .func = nop },
    Op{ .code = 0x01, .str = "LD", .destType = .reg16, .dest = .BC, .srcType = .imm16, .src = .none, .offset = 3, .tstates = 12, .func = ld },
    Op{ .code = 0x02, .str = "LD", .destType = .reg16ind, .dest = .BC, .srcType = .reg8, .src = .A, .offset = 1, .tstates = 8, .func = ld },
    Op{ .code = 0x03, .str = "INC", .destType = .reg16, .dest = .BC, .srcType = .none, .src = .none, .offset = 1, .tstates = 8, .func = inc16 },
    Op{ .code = 0x04, .str = "INC", .destType = .reg8, .dest = .B, .srcType = .none, .src = .none, .offset = 1, .tstates = 4, .func = inc8 },
    // ...
};

fn nop(_: *SM83, op: Op) void {
    std.debug.print("op: {s}\n should execute in {d} tstates\n", .{ op.str, op.tstates });
}

test "misc op: NOP" {
    var CPU = try SM83.init(std.testing.allocator);
    defer CPU.deinit(std.testing.allocator);

    nop(CPU, mainOps[0]);
}

fn ld(CPU: *SM83, op: Op) void {
    // a beefy one to start with : LD ops are almost half of the full operation set
    switch (op.srcType) {
        // process immediate register ops :
        .imm8 => {
            CPU.setR8(op.dest, CPU.imm8());
        },
        .imm16 => {
            CPU.setR16(op.dest, CPU.imm16());
        },
        .reg8 => {
            switch (op.destType) {
                .reg8 => {
                    // TODO: test
                    CPU.setR8(op.dest, CPU.r8(op.src));
                },
                .reg16ind => {
                    CPU.mem[CPU.r16(op.dest)] = CPU.r8(op.src);
                },
                else => unreachable,
            }
        },
        .reg16 => {
            // FIXME: test & enforce only one case ? (LD SP, HL)
            CPU.setR16(op.dest, CPU.r16(op.src));
        },
        else => unreachable,
    }
}

test "misc op: LD BC,1234H" {
    var CPU = try SM83.init(std.testing.allocator);
    defer CPU.deinit(std.testing.allocator);

    CPU.mem[0] = 0x01;
    CPU.mem[1] = 0x34;
    CPU.mem[2] = 0x12;
    ld(CPU, mainOps[1]);

    try expectEqual(0x1234, CPU.BC);
}

test "misc op: LD (BC),A" {
    var CPU = try SM83.init(std.testing.allocator);
    defer CPU.deinit(std.testing.allocator);

    CPU.setR8(.A, 0x42);
    CPU.BC = 0x1234;
    ld(CPU, mainOps[2]);

    try expectEqual(0x42, CPU.mem[CPU.BC]);
}

/// Increments a 16b register : no flags handling needed.
fn inc16(CPU: *SM83, op: Op) void {
    // doesn't check op validity (in op we trust)
    // handle overflow
    CPU.setR16(op.dest, CPU.r16(op.dest) +% 1);
}

/// Decrements a 16b register : no flags handling needed.
fn dec16(CPU: *SM83, op: Op) void {
    // doesn't check op validity (in op we trust)
    // handle overflow
    // FIXME: untested
    CPU.setR16(op.dest, CPU.r16(op.dest) -% 1);
}

test "misc op: INC BC" {
    var CPU = try SM83.init(std.testing.allocator);
    defer CPU.deinit(std.testing.allocator);

    CPU.BC = 0x1233;
    CPU.exec(mainOps[3]);

    try expectEqual(0x1234, CPU.BC);

    CPU.BC = 0xFFFF;
    CPU.exec(mainOps[3]);

    try expectEqual(0x0000, CPU.BC);
}

/// Increments 8b register: handles F register.
fn inc8(CPU: *SM83, op: Op) void {
    // FIXME: needs test harness before going further
    var value = CPU.r8(op.dest);
    value +%= 1;

    CPU.setR8(op.dest, value);
}
