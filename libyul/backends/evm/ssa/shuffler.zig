const std = @import("std");

const SlotType = enum(c_int) { variable, label, junk, returnLabel };
const Slot = extern struct { type: SlotType, val: u64 };
const Stack = extern struct { ptr: [*]const Slot, len: usize };

// export fn shuffle(inputStack: Stack, targetStack: Stack) void;
