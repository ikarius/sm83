const std = @import("std");
const expectEqual = std.testing.expectEqual;
const expect = std.testing.expect;

/// Update the most significant byte (*MSB*) of input word (u16).
pub fn setMSB(reg: u16, val: u8) u16 {
    return (reg & 0x00ff) | @as(u16, val) << 8;
}

/// Update the least significant byte (*LSB*) of input word (u16).
pub fn setLSB(reg: u16, val: u8) u16 {
    return (reg & 0xff00) | val;
}

test "set MSB/LSB" {
    const w = 0x1234;
    try expectEqual(0x1242, setLSB(w, 0x42));
    try expectEqual(0x4234, setMSB(w, 0x42));
}

/// Returns the most significant byte (*MSB*) of 16 bit register.
pub fn MSB(reg: u16) u8 {
    return @truncate((reg & 0xff00) >> 8);
}

/// Returns the least significant byte (*LSB*) of 16 bit register.
pub fn LSB(reg: u16) u8 {
    return @truncate(reg & 0x00ff);
}

test "MSB/LSB values" {
    const reg = 0x1234;
    try expectEqual(0x12, MSB(reg));
    try expectEqual(0x34, LSB(reg));
}

pub fn word(msb: u8, lsb: u8) u16 {
    return @as(u16, msb) << 8 | lsb;
}

test "word values" {
    try expectEqual(0x1234, word(0x12, 0x34));
}

/// Check if there is a *half-carry* (for addition)
/// or a *half-borrow* (for substraction)
/// performed when moving from `old` value to `new` value.
///
/// The `carry` parameter must be `true` for half-carry check, or `false` for half-borrow.
pub fn hc8(old: u8, new: u8, carry: bool) bool {
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

// Allume le bit à la position spécifiée
pub fn setBit(byte: u8, pos: u3) u8 {
    return byte | (@as(u8, 1) << pos);
}

// Éteint le bit à la position spécifiée
pub fn resetBit(byte: u8, pos: u3) u8 {
    return byte & ~(@as(u8, 1) << pos);
}

// Inverse le bit à la position spécifiée
pub fn toggleBit(byte: u8, pos: u3) u8 {
    return byte ^ (@as(u8, 1) << pos);
}

// Vérifie si un bit est allumé
pub fn isBit(byte: u8, pos: u3) bool {
    return (byte & (@as(u8, 1) << pos)) != 0;
}

// FIXME : add tests
