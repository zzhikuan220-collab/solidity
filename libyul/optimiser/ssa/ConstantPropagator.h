#pragma once

///In SSA form, constant propagation is simpler because each variable is defined exactly once.
/// You don’t need to worry about re‑assignments: each SSA name either has a constant initializer or inherits via φ‑nodes:
/// x1 = 5
/// x2 = φ(x1, x3)
/// x3 = x2 + 1
/// Here you’d see x1 ↦ 5, so if both φ‑operands for x2 are 5, you propagate 5 into x2, and then replace x3’s definition by x3 = 5 + 1 = 6.

/**
 To implement a fast, global constant‐propagation pass over an SSA CFG, you’ll want to combine:

1. **A sparse, worklist‐driven iteration** over only those variables and blocks whose “constant‐ness” might still change.
2. **A small finite lattice** per SSA name (⊥, a concrete constant, or ⊤ = “varies”).
3. **Efficient support for φ‑nodes** and conditional branches to both discover new constants and prune unreachable code.

Below is a blueprint you can adapt to your compiler’s IR:

---

## 1. Data structures

1. **Lattice map**

   ```cpp
   enum ConstValue { UNDEF, TOP, CONST };
   struct Lattice {
     ConstValue kind;
     Optional<Literal> value;  // Only set if kind == CONST
   };
   // map from SSA-def ID → Lattice
   DenseMap<DefID, Lattice> lattice;
   ```

2. **Worklists**

   * **Value‐worklist**: SSA definitions whose lattice just changed.
   * **Block‐worklist**: CFG blocks whose executable‐flag just became live (optional if doing SCCP).

3. **Executable flags** (for SCCP)

   ```cpp
   BitVector blockExecutable;   // whether a block is reachable under some constant‐prop context
   ```

4. **Def‐use chains & CFG**

   * For each use of a def, you need to revisit the using instruction when the def’s lattice changes.
   * For each φ‐node, you need to revisit it when any incoming edge’s lattice or reachability changes.

---

## 2. Lattice join operations

```cpp
// join two lattice values a, b
Lattice join(Lattice a, Lattice b) {
  if (a.kind == UNDEF)   return b;
  if (b.kind == UNDEF)   return a;
  if (a.kind == CONST && b.kind == CONST && a.value == b.value)
    return a;
  return { TOP, value=None };
}
```

---

## 3. Sparse Conditional Constant Propagation (SCCP)

SCCP both propagates constants **and** marks blocks reachable under those constants, so you can fold branches to eliminate dead code early.

### 3.1 Initialization

1. Mark the entry block executable:

   ```cpp
   blockExecutable[entry] = true;
   blockWorklist.push(entry);
   ```
2. Initialize all defs to `UNDEF`.

### 3.2 Main loop

```cpp
while (!valueWorklist.empty() || !blockWorklist.empty()) {
  // 1) Process newly executable blocks:
  while (!blockWorklist.empty()) {
    Block *B = blockWorklist.pop();
    for (Instruction &I : B->instructions())
      visitInstruction(I);
  }

  // 2) Process lattice updates:
  while (!valueWorklist.empty()) {
    DefID d = valueWorklist.pop();
    for (Use &u : defUseChains[d])
      visitInstruction(u.user);
  }
}
```

### 3.3 Visiting an instruction

```cpp
void visitInstruction(Instruction &I) {
  switch (I.opcode) {
    case CONST_INST:           // e.g. x = 42
      updateLattice(I.def, { CONST, .value = 42 });
      break;

    case BINARY_OP: {          // x = y + z
      Lattice Ly = lattice[y.def];
      Lattice Lz = lattice[z.def];
      Lattice Lnew = evaluateBinaryOp(Ly, Lz, I.opcode);
      updateLattice(I.def, Lnew);
      break;
    }

    case PHI: {                // x = φ(y1,B1; y2,B2; …)
      Lattice acc = { UNDEF };
      for each incoming (yi, Bi) {
        if (!blockExecutable[Bi]) continue;
        acc = join(acc, lattice[yi.def]);
      }
      updateLattice(I.def, acc);
      break;
    }

    case COND_BR: {            // br i1 c, Btrue, Bfalse
      Lattice Lc = lattice[c.def];
      if (Lc.kind == CONST) {
        // only one successor becomes executable:
        Block *take = (Lc.value != 0 ? Btrue : Bfalse);
        if (!blockExecutable[take]) {
          blockExecutable[take] = true;
          blockWorklist.push(take);
        }
      } else {
        // both successors:
        for (Block *succ : {Btrue, Bfalse})
          if (!blockExecutable[succ]) {
            blockExecutable[succ] = true;
            blockWorklist.push(succ);
          }
      }
      break;
    }

    case UNCOND_BR: {
      Block *succ = I.getSuccessor(0);
      if (!blockExecutable[succ]) {
        blockExecutable[succ] = true;
        blockWorklist.push(succ);
      }
      break;
    }

    // … handle other ops, calls, etc., conservatively producing TOP …
  }
}
```

### 3.4 The updateLattice helper

```cpp
void updateLattice(DefID d, Lattice newL) {
  Lattice oldL = lattice[d];
  Lattice joined = join(oldL, newL);
  if (joined.kind != oldL.kind ||
      (joined.kind == CONST && joined.value != oldL.value)) {
    lattice[d] = joined;
    valueWorklist.push(d);
  }
}
```

---

## 4. Post‐processing

1. **Replace uses**: For every def `d` with `lattice[d].kind == CONST`, replace its uses with the literal.
2. **Fold branches**: In each `br i1 c, T, F`, if `c` is constant, turn it into an unconditional jump to the “taken” block.
3. **Eliminate dead code**: Any block with `blockExecutable == false` can be removed.
4. **Dead‐def elimination**: Remove defs that became unused after propagation/folding.

---

## 5. Efficiency considerations

* **Sparse worklists**: Only instructions whose operands changed get revisited; this typically converges in **O(#defs + #edges + #uses)** steps.
* **Def‐use chains**: A sparse representation means you only scan real uses, not every instruction every time.
* **Early pruning** via SCCP\*\*: As soon as you see a branch constant, you stop analyzing the unreachable side of the CFG.
* **Bit‐packed lattice**: You can encode `UNDEF`/`CONST`/`TOP` in 2 bits and store small constants inline (e.g. 32‐bit immediate) for cache‐friendly access.

---

### Summary

1. **Model** each SSA name’s state in a 3‐point lattice.
2. **Iterate** using two small worklists (blocks & values) until no lattice or reachability changes occur.
3. **Exploit SSA**: φ‑nodes and def‐use chains let you propagate and fold in time proportional to actual use‐sites.

This SCCP‐style approach is what LLVM, GCC, and many industrial compilers use under the hood to get both **fast** compile times and **aggressive** constant folding.

 *
 **/
