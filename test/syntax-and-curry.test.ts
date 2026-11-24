import assert from "node:assert/strict";
import { test } from "node:test";
import {
  and,
  atom,
  bottom,
  checkRecursiveDefinition,
  equiv,
  exists,
  flip,
  forall,
  itemKey,
  or,
  ref,
  refl,
  structImposs,
  implies,
} from "../src/syntax.ts";

function test_role_indexed_atomic_items_and_reserved_forms(): void {
  const boilOrderA = atom("Boils", [
    { role: "substance", handle: "h2o" },
    { role: "pressure", handle: "1atm" },
  ]);
  const boilOrderB = atom("Boils", [
    { role: "pressure", handle: "1atm" },
    { role: "substance", handle: "h2o" },
  ]);
  assert.equal(itemKey(boilOrderA), itemKey(boilOrderB));

  const unary = atom("White", [{ role: "subject", handle: "swan_1" }]);
  assert.equal(unary.kind, "atom");
  assert.equal(itemKey(unary), "White(subject:swan_1)");

  const bot = bottom();
  assert.equal(bot.kind, "bottom");
  assert.equal(itemKey(bot), "⊥");

  const eq = equiv("B_macro", "river_t0", "river_t1");
  assert.equal(eq.kind, "equiv");
  assert.equal(itemKey(eq), "(river_t0 ≈_B_macro river_t1)");
}

function test_compound_items_and_structural_impossibility_shorthand(): void {
  const a = atom("A");
  const c = atom("C");
  const compound = forall(
    "x",
    "D",
    implies(and(a, flip(c)), or(a, exists("y", "D", equiv("D", "x", "y")))),
  );
  assert.equal(compound.kind, "forall");

  const imposs = structImposs(a);
  assert.equal(imposs.kind, "implies");
  if (imposs.kind === "implies") {
    assert.equal(imposs.antecedent, a);
    assert.equal(imposs.consequent.kind, "bottom");
  }
  assert.equal(itemKey(imposs), "(A() → ⊥)");

  const r = refl(0, "B", "+", a);
  assert.equal(r.kind, "refl");
  assert.equal(itemKey(r), "Refl_0(B ⊩+ A())");
}

function test_curry_firewall_blocks_all_four_vectors_and_allows_cross_stage(): void {
  const z = atom("MoonIsCheese");

  // Vector 1: K := K → Z (direct negative recursion left of →)
  const v1 = checkRecursiveDefinition({
    name: "K",
    level: 0,
    body: implies(ref("K"), z),
  });
  assert.equal(v1.ok, false);
  if (!v1.ok) {
    assert.equal(v1.violation, "left-of-implies");
  }

  // Vector 2: K_n := Refl_k(Σ ; B ⊩+ K_n) → Z (same-level reflection diagonal)
  const v2SameLevel = checkRecursiveDefinition({
    name: "K_n",
    level: 1,
    body: implies(refl(1, "B", "+", ref("K_n")), z),
  });
  assert.equal(v2SameLevel.ok, false);
  if (!v2SameLevel.ok) {
    assert.equal(v2SameLevel.violation, "stratification-violation");
  }

  const v2LowerK = checkRecursiveDefinition({
    name: "K_n",
    level: 1,
    body: implies(refl(0, "B", "+", ref("K_n")), z),
  });
  assert.equal(v2LowerK.ok, false);
  if (!v2LowerK.ok) {
    assert.equal(v2LowerK.violation, "stratification-violation");
  }

  // Valid cross-stage reflection: K_{t+1} := Refl_t(Σ_t ; B ⊩+ K_t) → Z is well-formed
  const known = new Map<string, number>([["K_t", 0]]);
  const crossStage = checkRecursiveDefinition(
    {
      name: "K_t1",
      level: 1,
      body: implies(refl(0, "B", "+", ref("K_t")), z),
    },
    known,
  );
  assert.equal(crossStage.ok, true);

  // Vector 3: K := (~K) → Z (polarity flip disguise)
  const v3 = checkRecursiveDefinition({
    name: "K",
    level: 0,
    body: implies(flip(ref("K")), z),
  });
  assert.equal(v3.ok, false);
  if (!v3.ok) {
    assert.equal(v3.violation, "polarity-flip");
  }

  // Vector 4: K := ∀(y : B ⊓ [K]) Z (contravariant boundary promotion)
  const v4 = checkRecursiveDefinition({
    name: "K",
    level: 0,
    body: forall("y", "B", z, ref("K")),
  });
  assert.equal(v4.ok, false);
  if (!v4.ok) {
    assert.equal(v4.violation, "boundary-promotion");
  }

  // Strictly positive recursive definition is permitted
  const positive = checkRecursiveDefinition({
    name: "Stream",
    level: 0,
    body: and(atom("Head"), ref("Stream")),
  });
  assert.equal(positive.ok, true);
}

test("role-indexed atomic items and reserved forms", test_role_indexed_atomic_items_and_reserved_forms);
test("compound items and structural impossibility shorthand", test_compound_items_and_structural_impossibility_shorthand);
test("Curry firewall blocks all four vectors and allows cross-stage reflection", test_curry_firewall_blocks_all_four_vectors_and_allows_cross_stage);
