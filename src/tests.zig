const std = @import("std");
const expectEqual = std.testing.expectEqual;
const word = @import("logic.zig").word;

const SM83 = @import("SM83.zig").SM83;

const test_path = "./tests/sm83/v1";

// This file reads a serie of JSON files,
// each containing 1000 tests for a given SM83 instruction.

const OpTest = struct {
    name: []const u8,
    initial: CpuState,
    final: CpuState,
};

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

/// Loads test data into the CPU.
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

/// Compares the current CPU state with the final state.
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

    // TODO: tstates ?
    // t-states are not in the test suite (only complete cycles)
    // they can be calculated from the cycles count and types.

    for (final.ram) |ram| {
        try expectEqual(ram[1], CPU.mem[ram[0]]);
    }
}

/// Loads the test data into the CPU, executes the operation,
/// then compares the CPU state with the final state.
fn checkCPUState(CPU: *SM83, optest: OpTest) !void {
    loadCpuState(CPU, optest.initial);
    CPU.execAt(optest.initial.pc);
    try compareCpuState(CPU, optest.final);
}

test "Open sample file (NOP)" {
    const allocator = std.testing.allocator;
    const result = try parseJsonFile(allocator, test_path ++ "/00.json");
    defer result.deinit();

    const opsuite = result.value;

    try expectEqual(1000, opsuite.len);

    // std.debug.print("name: {s}\n", .{opsuite[0].name});
    // std.debug.print("initial: {any}\n", .{opsuite[0].initial});
    // std.debug.print("final: {any}\n", .{opsuite[0].final});
}

fn testOpNumber(opNumber: u8) !void {
    const allocator = std.testing.allocator;
    const filePath = std.fmt.allocPrint(allocator, test_path ++ "/{x:0>2}.json", .{opNumber}) catch unreachable;
    defer allocator.free(filePath);

    std.debug.print("Testing op file '{s}'\n", .{filePath});

    const testSuite = try parseJsonFile(allocator, filePath);
    defer testSuite.deinit();

    for (testSuite.value, 0..) |optest, i| {
        var CPU = SM83{};

        checkCPUState(&CPU, optest) catch |err| {
            // More details if there is an error:
            std.debug.print("Running Test number {d}: {s}\n", .{ i, optest.name });
            std.debug.print("name: {s}\n", .{optest.name});
            std.debug.print("initial: {any}\n", .{optest.initial});
            std.debug.print("final: {any}\n\n", .{optest.final});

            return err;
        };
    }
}

test "Open test file by number" {
    for (0xd0..0xe0) |i| {
        // skip prefixed ops
        if (i == 0xcb) continue;
        testOpNumber(@truncate(i)) catch |err| {
            switch (err) {
                error.FileNotFound => {
                    std.debug.print(" > Unknown test file: `{x:0>2}.json`, passing...\n", .{i});
                },
                else => return err,
            }
        };
    }

    // Misc tests
    // try testOpNumber(0x40);
}
