const std = @import("std");

const expectEqual = std.testing.expectEqual;

const word = @import("logic.zig").word;

const root = @import("root.zig");
const SM83 = root.SM83;
const execAt = root.execAt;

// This file reads a serie of JSON files,
// each containing 1000 tests for a given SM83 instruction.
const CpuState = struct {
    pc: u16,
    sp: u16,
    a: u8,
    b: u8,
    c: u8,
    d: u8,
    e: u8,
    f: u8,
    h: u8,
    l: u8,
    ime: u8,
    ie: ?u8 = null, // needs = null or fails for optional fields
    ram: [][2]u16,
};

const OpTest = struct {
    name: []const u8,
    initial: CpuState,
    final: CpuState,
};

const test_path = "./tests/sm83/v1";

fn loadCpuState(CPU: *SM83, state: CpuState) void {
    CPU.reset();
    CPU.AF = word(state.a, state.f);
    CPU.BC = word(state.b, state.c);
    CPU.DE = word(state.d, state.e);
    CPU.HL = word(state.h, state.l);
    CPU.SP = state.sp;
    CPU.PC = state.pc;

    for (state.ram) |ram| {
        CPU.mem[ram[0]] = @truncate(ram[1]);
    }
}

fn compareCpuState(CPU: *SM83, final: CpuState) !void {
    try expectEqual(final.a, CPU.A());
    try expectEqual(final.f, CPU.F());
    try expectEqual(final.b, CPU.B());
    try expectEqual(final.c, CPU.C());
    try expectEqual(final.d, CPU.D());
    try expectEqual(final.e, CPU.E());
    try expectEqual(final.h, CPU.H());
    try expectEqual(final.l, CPU.L());
    try expectEqual(final.sp, CPU.SP);
    try expectEqual(final.pc, CPU.PC);

    for (final.ram) |ram| {
        try expectEqual(ram[1], CPU.mem[ram[0]]);
    }
}

fn checkCPUState(CPU: *SM83, optest: OpTest) !void {
    loadCpuState(CPU, optest.initial);
    CPU.execAt(optest.initial.pc);
    try compareCpuState(CPU, optest.final);
}

/// Reads the test JSON file and returns a list of `OpTest` objects (generally 1000 of them).
fn parseJsonFile(allocator: std.mem.Allocator, filename: []const u8) !std.json.Parsed([]OpTest) {
    var file = try std.fs.cwd().openFile(filename, .{});
    defer file.close();

    const contents = try file.readToEndAlloc(allocator, std.math.maxInt(usize));
    defer allocator.free(contents);

    const result = try std.json.parseFromSlice([]OpTest, allocator, contents, .{
        .ignore_unknown_fields = true,
        // `alloc_always` is needed because `contents` is released after parsing
        // so we need to allocate (and keep them).
        .allocate = .alloc_always,
    });

    return result;
}

test "Open sample file (NOP)" {
    const allocator = std.testing.allocator;
    const result = try parseJsonFile(allocator, test_path ++ "/00.json");
    defer result.deinit();

    const opsuite = result.value;

    try expectEqual(1000, opsuite.len);

    std.debug.print("name: {s}\n", .{opsuite[0].name});
    std.debug.print("initial: {any}\n", .{opsuite[0].initial});
    std.debug.print("final: {any}\n", .{opsuite[0].final});
}

fn testOpNumber(opNumber: u8) !void {
    const allocator = std.testing.allocator;
    const filePath = std.fmt.allocPrint(allocator, test_path ++ "/{X:0>2}.json", .{opNumber}) catch unreachable;
    defer allocator.free(filePath);

    std.debug.print("Testing op file '{s}'\n", .{filePath});

    const testSuite = try parseJsonFile(allocator, filePath);
    defer testSuite.deinit();

    const CPU = try SM83.init(allocator);
    defer CPU.deinit(allocator);

    for (testSuite.value, 0..) |optest, i| {
        std.debug.print("Running Test number {d}: {s}\n", .{ i + 1, optest.name });
        // std.debug.print("name: {s}\n", .{optest.name});
        std.debug.print("initial: {any}\n", .{optest.initial});
        std.debug.print("final: {any}\n", .{optest.final});

        try checkCPUState(CPU, optest);
    }
}

test "Open test file by number" {
    // try testOpNumber(0x00);
    // try testOpNumber(0x01);
    // try testOpNumber(0x02);
    // try testOpNumber(0x03);
    try testOpNumber(0x04);
}
