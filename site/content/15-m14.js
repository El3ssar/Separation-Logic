/* M14 — Optional — allocation
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m14",
  "num": "M14",
  "phase": "Phase 3 · Advanced separation logic",
  "title": "Optional — allocation",
  "blurb": "Adding malloc without destroying the frame rule.",
  "orient": {
    "youWill": [
      "Add an <code>alloc</code> constructor to <code>Cmd</code> and <code>Exec</code> and point at the single implicit binder that makes execution nondeterministic.",
      "Say why <code>Hoare P c Q := ∀ σ h, P σ h → ∃ s', …</code> stops being the definition you wanted, and read the eight-line proof that under it you can specify which location <code>malloc</code> returns.",
      "State and prove the small-footprint allocation rule, with the existential in the place the semantics forces it to be.",
      "Discover that <code>HeapLocal (.alloc x e)</code> is <b>false</b>, produce the two-cell counterexample, and replace it with the frame property — the same condition with the quantification reversed — which is true.",
      "Verify <code>alloc; write; load; free</code> end to end and see the difference between “choose a run” and “invert every run” in the same proof."
    ],
    "needs": [
      "M8: <code>HeapLocal</code>, <code>Preserves</code>, and the shape of <code>hoare_frame</code>'s proof. This chapter is mostly about how that definition has to change.",
      "M6: <code>Hoare</code> as total correctness, <code>Exec</code> as an inductive relation, and <code>exec_deterministic</code> — which is the theorem that dies first.",
      "M2: <code>Heap.disjoint</code>, <code>Heap.union</code>, <code>union_eq_none</code>, <code>union_of_none</code> / <code>union_of_some</code>. The whole locality argument is one application of <code>union_eq_none</code>.",
      "M13's closing note on address expressions: <code>load</code>, <code>write</code> and <code>free</code> take a literal <code>Loc</code>, which is unusable once the address comes out of <code>alloc</code>. The refactor is folded in here.",
      "Tactically: <code>cases … with | @ctor …</code> to name implicit arguments produced by inversion, <code>show</code> to restate a goal at a definitionally equal type, and <code>clear</code>."
    ],
    "payoff": "Every separation logic you will meet has an allocation rule with an existentially quantified pointer, and almost none of them explain why. After this chapter you can derive that design from the failure of a specific proof obligation, and you can say exactly which of the two halves of locality your heap representation is buying you."
  },
  "blocks": [
    {
      "t": "note",
      "kind": "warn",
      "title": "This chapter is optional, and it modifies rather than extends",
      "h": "Every other chapter quotes <code>lean/corpus.lean</code>, which is machine-checked as one file. This chapter cannot: it <i>changes the language</i>, and Lean's inductive types are closed — there is no way to add a constructor to <code>Cmd</code> after the fact. So everything below lives in <code>namespace M14</code>, where <code>Cmd</code>, <code>Exec</code>, <code>Hoare</code>, <code>HeapLocal</code> and friends are <i>redeclared</i>, shadowing the M0–M13 versions. Heaps, assertions, <code>∗</code>, <code>emp</code>, <code>↦</code> and the whole of Phase 1 are untouched and still in scope. Every <i>complete</i> snippet below was checked under Lean 4.32.2 against everything defined through M13 and is tagged <b>illustration</b>; fragments of a larger declaration are tagged <b>sketch</b>; the single block tagged <b>verified</b> is a quotation of M9's <code>hoare_write_val</code> from the corpus, put there for comparison. One practical note if you reproduce this yourself: <code>site/lean/prelude/m13.lean</code> ends with M13's forward-looking sketch of the address-expression language — a second <code>inductive Cmd</code> and a statement of <code>hoare_load'</code> with no proof — so cut those two blocks before you append anything of your own."
    },
    {
      "t": "p",
      "h": "Because it is a modification, it has a bill, and you should see the bill before you decide to work through the chapter. Redeclaring <code>Cmd</code> means every statement in M5–M13 that mentions <code>Cmd</code>, <code>Exec</code>, <code>Hoare</code> or <code>wp</code> has to be restated inside the new namespace. Most of that is copy-and-paste, and most of the proofs survive it unchanged: they invert an execution of one <i>named</i> command, so an extra constructor only adds a case that never fires. Four things are not copy-and-paste:"
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "M5 · <code>exec_deterministic</code>",
          "h": "Not re-proved — <b>refuted</b>. Exercise 1 is the disproof. Anything that took it as an argument has to find another route."
        },
        {
          "k": "M13 · <code>partial_of_total</code>",
          "h": "Its M13 proof runs the total triple, gets one final state, and uses <code>exec_deterministic</code> to identify it with the arbitrary <code>s'</code> it was handed. That route is gone. Under the definition of <code>Hoare</code> this chapter arrives at, the theorem is a projection instead — cheaper than what it replaces."
        },
        {
          "k": "M8 · <code>hoare_frame</code>",
          "h": "The statement survives; the hypothesis does not. M8's single <code>hlocal : HeapLocal c</code> has to be split into two independent conditions, and over functional heaps <code>alloc</code> satisfies exactly one of them. The <code>heapLocal_*</code> lemmas for <code>skip</code>, <code>assign</code>, <code>load</code>, <code>write</code>, <code>free</code> and <code>seq</code> stay true of their own commands; they are simply no longer the hypothesis you want to have proved."
        },
        {
          "k": "M12 · <code>wp</code>",
          "h": "<code>wp c Q := fun σ h => ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>, and <code>hoare_iff_entails_wp</code> is <code>Iff.rfl</code> — the two definitions are literally the same expression. Change <code>Hoare</code> and that <code>rfl</code> stops type-checking until you change <code>wp</code> to match. The angelic/demonic distinction below is a distinction about <code>wp</code> too."
        }
      ]
    },
    {
      "t": "h3",
      "s": "The problem"
    },
    {
      "t": "p",
      "h": "Every heap in this course has been created by assumption; nothing ever allocates. Adding allocation is where a naïve design breaks the frame rule, so it is worth doing carefully."
    },
    {
      "t": "p",
      "h": "Suppose you add “allocate exactly location <code>l</code>”. Then"
    },
    {
      "t": "txt",
      "src": "  { emp }  alloc-at l  { l ↦ 0 }\n\n  frame with  l ↦ 7 :\n\n  { emp ∗ l ↦ 7 }  alloc-at l  { l ↦ 0 ∗ l ↦ 7 }     ← postcondition is FALSE"
    },
    {
      "t": "p",
      "h": "The postcondition is unsatisfiable, so the framed triple is vacuously… no: the <i>precondition</i> is satisfiable and the command runs, so the triple is genuinely false. The command is not local: its behaviour depends on memory it does not own."
    },
    {
      "t": "note",
      "kind": "key",
      "title": "The one thing to remember",
      "h": "Locality is a property you can lose. The frame rule is only available to languages whose commands cannot observe or collide with memory outside their footprint. Allocation is the standard place where this is tested."
    },
    {
      "t": "h3",
      "s": "Three things break, and only the first one is obvious"
    },
    {
      "t": "p",
      "h": "The paragraph above is the version of this story everybody tells: name a location in the specification and the frame rule dies. It is true, and it is the least of the damage. When you actually type the extension into Lean, three separate things stop working, in this order."
    },
    {
      "t": "steps",
      "title": "What allocation costs you",
      "items": [
        {
          "k": "The <i>definition</i> of the triple",
          "h": "<code>Exec</code> stops being a partial function of the starting state, so <code>exec_deterministic</code> is false. That is a nuisance. What is worse is that <code>Hoare P c Q := ∀ σ h, P σ h → ∃ s', Exec c ⟨σ,h⟩ s' ∧ Q s'</code> silently changes meaning. With one possible outcome, “∃ a good outcome” and “all outcomes are good” coincide. With several, <code>∃</code> is the <b>angelic</b> reading, and it is wrong: it lets you prove that the allocator returns location <code>0</code>."
        },
        {
          "k": "<code>HeapLocal</code>",
          "h": "M8's locality condition says: given a run on the small heap, its result is disjoint from the frame, and the same command can be run on the big heap with that result plus the frame. For allocation this is <b>false</b>, and it fails at the first clause, before the big heap is even mentioned — in the small heap the allocator may pick a location the frame already owns, and then the result is not disjoint from anything. This is not a defect in the specification; it is a defect in the <i>direction</i> the condition quantifies."
        },
        {
          "k": "<code>Heap := Loc → Option Val</code>",
          "h": "A heap in this course is an arbitrary function, so <code>fun _ => some 0</code> is a legal heap with no free location at all. Allocation on it is stuck. That kills <b>safety monotonicity</b> — “safe on a small heap implies safe on a bigger one” — which the frame rule also needs. This is the real reason to move to finite heaps, and it is not an implementation convenience."
        }
      ]
    },
    {
      "t": "p",
      "h": "Exercise 1 is the first failure, exercise 3 is the second and third, and exercise 4 is what the repaired machinery buys you. Everything below is a worked answer, not the only one."
    },
    {
      "t": "h3",
      "s": "Option A · nondeterministic fresh allocation"
    },
    {
      "t": "code",
      "src": "| alloc : Var → Atom → Cmd\n\n-- semantics: choose ANY unallocated location, store the value there,\n-- and put the location in the destination variable.\n\ntheorem hoare_alloc :\n    Hoare emp (.alloc x e)\n      (aExists fun l => pure (fun σ => σ x = l) ∗ (l ↦ e.eval σ))",
      "tag": "sketch",
      "cap": "The original sketch. Two things in it need repair — see below."
    },
    {
      "t": "p",
      "h": "The existential over <code>l</code> is not cosmetic: it is <b>required</b> for locality. Framing changes which locations are already taken, hence which one the allocator picks — so no specification that names a particular location can be local."
    },
    {
      "t": "p",
      "h": "Consequences to be aware of: <code>Exec</code> stops being deterministic, so <code>exec_deterministic</code> and everything derived from it (including <code>partial_of_total</code>) must be revisited, and the interpreter needs an allocation strategy fixed as a parameter."
    },
    {
      "t": "h4",
      "s": "The constructor, written out"
    },
    {
      "t": "p",
      "h": "Here is the rule as Lean actually accepts it. Read it against any other constructor of <code>Exec</code> and one difference will jump out."
    },
    {
      "t": "anat",
      "src": "  | alloc {s x e l} (hfresh : s.heap l = none) :\n      Exec (.alloc x e) s ⟨Store.set s.store x l, Heap.write s.heap l (e.eval s.store)⟩",
      "tag": "sketch",
      "cap": "One constructor lifted out of the <code>Exec</code> declaration; it compiles as part of that declaration, printed in full under exercise 1, not on its own.",
      "parts": [
        {
          "m": "{s x e l}",
          "h": "Four implicit binders. Three of them — <code>s</code>, <code>x</code>, <code>e</code> — are fixed the moment you know the starting state and the command. <code>l</code> is not. It appears in the conclusion but nothing outside this constructor determines it. That single free binder <i>is</i> the nondeterminism."
        },
        {
          "m": "(hfresh : s.heap l = none)",
          "h": "The only constraint on <code>l</code>: the cell must currently be unallocated. Note what is <i>not</i> here — no “least such <code>l</code>”, no allocator state, no bump pointer. Adding any of those would make <code>Exec</code> deterministic again and would immediately reintroduce the counterexample at the top of this chapter."
        },
        {
          "m": "Store.set s.store x l",
          "h": "The chosen location is handed back through the store, in variable <code>x</code>. This is why allocation is the one heap primitive that also writes a variable."
        },
        {
          "m": "Heap.write s.heap l (e.eval s.store)",
          "h": "The heap grows by one cell. <code>Heap.write</code> is total — it does not care whether the cell existed — which is exactly why <code>hfresh</code> has to be supplied separately. On paper you would say “extend the heap”; in Lean extension and overwrite are the same operation and the difference is a hypothesis."
        }
      ]
    },
    {
      "t": "cmp",
      "left": {
        "t": "Every other constructor",
        "kind": "good",
        "h": "The resulting state is a <i>function</i> of the command and the starting state. Here <code>old</code> is mentioned in the premise but never in the conclusion: the outcome does not depend on it. <code>load</code> looks like a counterexample — its implicit <code>v</code> <i>does</i> appear in the conclusion — but its premise <code>s.heap (a.eval s.store) = some v</code> pins <code>v</code> to a single value, so the state is still determined.",
        "src": "  | write {s a e old} (hl : s.heap (a.eval s.store) = some old) :\n      Exec (.write a e) s ⟨s.store, Heap.write s.heap (a.eval s.store) (e.eval s.store)⟩",
        "tag": "sketch"
      },
      "right": {
        "t": "The alloc constructor",
        "h": "<code>l</code> is mentioned in the conclusion and constrained only by <code>hfresh</code>. Two applications of the constructor with different <code>l</code> give two different final states from the same starting state. That is the whole of the disproof of <code>exec_deterministic</code>; everything else in exercise 1 is bookkeeping around it.",
        "src": "  | alloc {s x e l} (hfresh : s.heap l = none) :\n      Exec (.alloc x e) s ⟨Store.set s.store x l, Heap.write s.heap l (e.eval s.store)⟩",
        "tag": "sketch"
      }
    },
    {
      "t": "h4",
      "s": "What “∃ s'” means once there is more than one s'"
    },
    {
      "t": "p",
      "h": "M6 defined <code>Hoare P c Q</code> as “from any <code>P</code>-state there <i>exists</i> a final state, and it satisfies <code>Q</code>”. Read that sentence again with a nondeterministic command in mind. It says the command <i>can</i> behave well, not that it <i>must</i>."
    },
    {
      "t": "p",
      "h": "Separating the two readings needs a name for “does not get stuck”, which M6 never had to give because its <code>∃ s'</code> carried that meaning as a side effect. Give it one:"
    },
    {
      "t": "code",
      "src": "def Safe (c : Cmd) (s : State) : Prop := ∃ s', Exec c s s'",
      "tag": "illustration",
      "cap": "There is at least one run. Nothing about where it ends."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Angelic — the M6 definition, unchanged",
        "kind": "bad",
        "h": "“There is a run that lands in <code>Q</code>.” Fine while <code>Exec</code> is a partial function; nonsense once it is not. The prover gets to choose the run, so the prover gets to choose the location.",
        "src": "def AngelicHoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap",
        "tag": "illustration"
      },
      "right": {
        "t": "Demonic — safety plus universal correctness",
        "kind": "good",
        "h": "“At least one run exists, and <i>every</i> run lands in <code>Q</code>.” Two obligations instead of one. The first is safety (the command is not stuck); the second is M13's <code>PartialHoare</code>, up to the order the binders come in — M13 writes <code>∀ σ h s', P σ h → Exec … → Q</code>, and here <code>s'</code> arrives after the proof of <code>P</code> rather than before.",
        "src": "def Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h →\n    Safe c ⟨σ, h⟩ ∧ ∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap",
        "tag": "illustration"
      }
    },
    {
      "t": "p",
      "h": "The angelic reading is not merely weaker in theory. It proves the specification the top of this chapter said was impossible — that allocation returns location <code>0</code> — and the proof is eight lines, none of them clever:"
    },
    {
      "t": "code",
      "src": "theorem angelic_alloc_names_zero (x : Var) (v : Val) :\n    AngelicHoare emp (.alloc x (.const v)) (pure (fun σ => σ x = 0) ∗ (0 ↦ v)) := by\n  intro σ h he\n  subst he\n  refine ⟨⟨Store.set σ x 0, Heap.write Heap.empty 0 v⟩, Exec.alloc (l := 0) rfl, ?_⟩\n  refine ⟨Heap.empty, Heap.singleton 0 v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩\n  · show Heap.write Heap.empty 0 v = Heap.union Heap.empty (Heap.singleton 0 v)\n    rw [union_empty_left, write_empty]\n  · show Store.set σ x 0 x = 0\n    simp [Store.set]",
      "tag": "illustration",
      "cap": "Under the angelic reading you may name the location. This theorem is true and useless."
    },
    {
      "t": "p",
      "h": "Nothing is wrong with the proof. What is wrong is the definition it satisfies. A specification that is provable because the prover picks the run is not a specification of the program. Once you switch to the demonic reading, <code>Safe</code> and the <code>∀ s'</code> clause pull in opposite directions and the existential in the postcondition becomes forced."
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "One thing you get back for free",
      "h": "M13 proved <code>partial_of_total</code> by running the total triple, obtaining <i>a</i> final state, and invoking <code>exec_deterministic</code> to identify it with the arbitrary <code>s'</code> it was handed. Under the demonic definition no such argument is needed: partial correctness is the second conjunct, so the whole proof is <code>fun σ hh s' hp hex => (h σ hh hp).2 s' hex</code> — reorder the binders and project. You lose determinism and gain a definition that never wanted it."
    },
    {
      "t": "h3",
      "s": "Option B · finite heaps"
    },
    {
      "t": "code",
      "src": "abbrev Heap := List (Loc × Val)   -- with a no-duplicate-keys invariant",
      "tag": "sketch"
    },
    {
      "t": "p",
      "h": "With finite heaps you can <i>prove</i> that a fresh location exists (take one greater than the maximum key), so allocation becomes deterministic and executable. The price is that every M1–M2 lemma has to be redone: lookup, insert, delete, disjointness, and — the painful one — heap extensionality, which is no longer <code>funext</code> but a lemma about lists modulo permutation."
    },
    {
      "t": "h4",
      "s": "Why Option B is not a convenience"
    },
    {
      "t": "p",
      "h": "The sentence above makes finiteness sound like an engineering preference. It is not. With <code>Heap := Loc → Option Val</code> a heap is an arbitrary function, and <code>fun _ => some 0</code> is a perfectly good one. Allocation on that heap has no move. So the following is a theorem:"
    },
    {
      "t": "code",
      "src": "def SafetyMonotone (c : Cmd) : Prop :=\n  ∀ σ h hFrame, Heap.disjoint h hFrame → Safe c ⟨σ, h⟩ → Safe c ⟨σ, Heap.union h hFrame⟩\n\ntheorem alloc_not_safetyMonotone (x : Var) (v : Val) :\n    ¬ SafetyMonotone (.alloc x (.const v)) := by\n  intro hmono\n  obtain ⟨r, hex⟩ :=\n    hmono (fun _ => 0) Heap.empty (fun _ => some 0)\n      (disjoint_empty_left _) ⟨_, Exec.alloc (l := 0) rfl⟩\n  cases hex with\n  | @alloc _ _ _ l hfresh =>\n      have hf : Heap.union Heap.empty (fun _ => some 0) l = none := hfresh\n      rw [union_empty_left] at hf\n      exact absurd hf (by simp)",
      "tag": "illustration",
      "cap": "Safety monotonicity fails. The frame is the total heap; the small heap is empty."
    },
    {
      "t": "p",
      "h": "Safety monotonicity is one of the two halves of locality in the standard presentation, and the frame rule needs it: to frame a triple you must know that a command safe on its own footprint is still safe when the rest of memory is there. For <code>load</code>, <code>write</code> and <code>free</code> it is trivial — adding cells never removes the one you were going to touch. For <code>alloc</code> it is exactly what fails, and moving to finite heaps is what repairs it."
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Which to pick",
      "h": "Both options are genuinely worth doing, and they teach different things. Option A teaches you what locality really demands. Option B teaches you how much of your development was secretly relying on the convenience of functional heaps. If you do only one, do A: it is a hundred lines and it changes how you read the frame rule."
    },
    {
      "t": "h3",
      "s": "What replaces HeapLocal"
    },
    {
      "t": "p",
      "h": "M8's <code>HeapLocal</code> reads: given a run on the small heap, the same run happens on the big heap and leaves the frame alone. For allocation the first conjunct alone is already false, because in the small heap the allocator may pick a location that the frame owns — and then the resulting heap is not disjoint from the frame at all. The fix is to quantify the other way round."
    },
    {
      "t": "cmp",
      "left": {
        "t": "Small → big (M8's <code>HeapLocal</code>)",
        "kind": "bad",
        "h": "You are handed a run on <code>h</code> and must produce a matching run on <code>h ∪ hFrame</code>. For <code>alloc</code> there is nothing to produce: the small run may have taken a cell the frame is using.",
        "src": "    Exec c ⟨σ, h⟩ s' →\n    Heap.disjoint s'.heap hFrame ∧\n    ∃ r, Exec c ⟨σ, Heap.union h hFrame⟩ r ∧ …",
        "tag": "sketch"
      },
      "right": {
        "t": "Big → small (the <b>frame property</b>)",
        "kind": "good",
        "h": "You are handed a run on <code>h ∪ hFrame</code> and must produce the matching run on <code>h</code>. Now it works: a location fresh in the union is fresh in <code>h</code>, so the small heap can make the same choice.",
        "src": "    Exec c ⟨σ, Heap.union h hFrame⟩ r →\n    ∃ s', Exec c ⟨σ, h⟩ s' ∧\n      Heap.disjoint s'.heap hFrame ∧ …",
        "tag": "sketch"
      }
    },
    {
      "t": "p",
      "h": "This is not a trick to make a proof go through. Under the demonic reading the frame rule genuinely needs both directions, and it needs them in different places:"
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "Safety monotonicity",
          "h": "Small → big, but only about <i>existence</i> of a run. Discharges the <code>Safe</code> obligation of the framed triple. <b>Fails for alloc over functional heaps.</b>"
        },
        {
          "k": "The frame property",
          "h": "Big → small, about the shape of every run. Discharges the <code>∀ s'</code> obligation: any big run comes from a small run plus an untouched frame. <b>Holds for alloc.</b>"
        },
        {
          "k": "<code>Preserves c R</code>",
          "h": "Unchanged from M8, and it cannot break: the definition quantifies over runs but never inspects the heap, so adding a heap primitive cannot affect it. The frame assertion may mention the store, and the command may write the store, so something has to rule out interference. For <code>alloc x e</code> the store <i>is</i> written, at <code>x</code>. M8's <code>preserves_of_heapOnly</code> still discharges the obligation for free whenever <code>R</code> is <code>HeapOnly</code> — its proof never mentions <code>Exec</code> — and <code>HeapOnly</code> covers <code>↦</code>, <code>emp</code>, and any <code>∗</code> of those, which is every frame you are likely to want. The frames it does not cover are the ones that talk about the store, such as <code>pure (fun σ => σ x = 7)</code>; those are exactly the ones allocation can falsify."
        }
      ]
    },
    {
      "t": "p",
      "h": "Together they give the frame rule back, with the same conclusion as M8 — though <code>Hoare</code> now means the demonic thing, and M8's single <code>hlocal</code> has become two hypotheses — and a proof nine lines long against M8's eight. It is proved as an exercise below; the point to carry away is that the three hypotheses are separate, that <code>alloc</code> satisfies the second and third, and that the missing first one is precisely the gap Option B fills."
    },
    {
      "t": "sec",
      "s": "Exercises (open)"
    },
    {
      "t": "p",
      "h": "These four are open projects rather than fill-in-the-blank proofs: there is no single right formulation, and the interesting part is what you discover while choosing one. Each exercise below carries a complete worked answer under <b>Why it works</b> — definitions, proofs and real goal states — but it is one design, not the design. Try yours first."
    },
    {
      "t": "ex",
      "id": "m14-1",
      "name": "add nondeterministic allocation",
      "hard": false,
      "why": "Extend <code>Cmd</code> and <code>Exec</code>; note where determinism breaks. This is the exercise where you find out that adding a constructor is the easy half, and that the hard half is that a definition you wrote in M6 has quietly changed meaning.",
      "setup": "Work in a fresh <code>namespace</code>: Lean inductives are closed, so you cannot add a constructor to the existing <code>Cmd</code> — you redeclare it with the extra case and shadow the old one. Take M13's address-expression refactor at the same time (<code>load : Var → Atom → Cmd</code>, <code>write : Atom → Atom → Cmd</code>, <code>free : Atom → Cmd</code>); you will need it, because after <code>alloc x e</code> the only handle you have on the new cell is the variable <code>x</code>. Then state and prove that <code>Exec</code> is no longer deterministic.",
      "hints": [
        "Look at every existing constructor of <code>Exec</code> and ask: is the final state a function of the command and the starting state? Then write the alloc rule so that the answer becomes no, and identify the single binder responsible.",
        "To <i>state</i> that determinism fails, do not try to negate <code>exec_deterministic</code> in place — negate its statement. <code>¬ ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂</code>.",
        "For the witness, take the empty heap, where <i>every</i> location is fresh, and run <code>alloc x (.const 0)</code> twice, once choosing <code>0</code> and once choosing <code>1</code>. Lean cannot guess which location you mean, so write <code>Exec.alloc (l := 0) rfl</code>.",
        "From the two states being equal, apply <code>congrArg (fun s => s.store x)</code> to get <code>Store.set … x 0 x = Store.set … x 1 x</code>, then <code>simp [Store.set]</code> reduces it to <code>0 = 1</code> and closes the goal by <code>Nat</code> no-confusion."
      ],
      "expl": "Adding the constructor takes one line. The content of the exercise is the disproof of determinism, and the reason it is worth writing out is that it is the smallest concrete object that shows why the M6 definition of <code>Hoare</code> can no longer be read the way you have been reading it.",
      "walk": [
        {
          "tac": "intro hdet",
          "h": "The goal is a negation, which in Lean is <code>… → False</code>. So <code>intro</code> works on it directly: it names the determinism assumption <code>hdet</code> and leaves you with <code>⊢ False</code>."
        },
        {
          "tac": "have h : (⟨Store.set (fun _ => 0) x 0, Heap.write Heap.empty 0 0⟩ : State) = …",
          "h": "Instantiate <code>hdet</code> at the empty heap with two runs of the same command. The explicit type annotation is not decoration: without it Lean displays the hypothesis as an unreduced pile of <code>{ store := … }.store</code> projections. Writing the type you want makes Lean check it up to definitional equality and then show you the readable form."
        },
        {
          "tac": "  hdet (.alloc x (.const 0)) ⟨fun _ => 0, Heap.empty⟩ _ _",
          "h": "The two final states are passed as <code>_ _</code> because they are determined by the two <code>Exec</code> proofs that follow."
        },
        {
          "tac": "    (Exec.alloc (l := 0) rfl) (Exec.alloc (l := 1) rfl)",
          "h": "Two applications of the same constructor differing only in the named argument <code>l</code>. The freshness proof is <code>rfl</code> in both cases: <code>Heap.empty l = none</code> holds by unfolding <code>Heap.empty</code>."
        },
        {
          "tac": "have h01 := congrArg (fun s => s.store x) h",
          "h": "Two states cannot be equal if a component differs. <code>congrArg f h</code> turns <code>a = b</code> into <code>f a = f b</code>; here <code>f</code> reads the store at <code>x</code>, giving <code>0 = 1</code> once the projections reduce."
        },
        {
          "tac": "simp [Store.set] at h01",
          "h": "<code>simp</code> unfolds <code>Store.set</code>, evaluates both <code>if x = x</code> tests, arrives at <code>(0 : Nat) = 1</code>, recognises it as impossible by constructor injectivity, and closes the goal. When <code>simp … at h</code> reduces a hypothesis to <code>False</code> it discharges the goal outright — which is why there is no final tactic."
        }
      ],
      "deep": [
        {
          "t": "p",
          "h": "The language, with the alloc case and M13's address expressions folded in:"
        },
        {
          "t": "code",
          "src": "inductive Cmd where\n  | skip\n  | assign : Var  → Atom → Cmd\n  | load   : Var  → Atom → Cmd\n  | write  : Atom → Atom → Cmd\n  | free   : Atom → Cmd\n  | alloc  : Var  → Atom → Cmd\n  | seq    : Cmd → Cmd → Cmd\n  | ite    : BExpr → Cmd → Cmd → Cmd\n  | loop   : BExpr → Cmd → Cmd",
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": "inductive Exec : Cmd → State → State → Prop where\n  | skip {s} : Exec .skip s s\n  | assign {s x e} :\n      Exec (.assign x e) s ⟨Store.set s.store x (e.eval s.store), s.heap⟩\n  | load {s x a v} (hl : s.heap (a.eval s.store) = some v) :\n      Exec (.load x a) s ⟨Store.set s.store x v, s.heap⟩\n  | write {s a e old} (hl : s.heap (a.eval s.store) = some old) :\n      Exec (.write a e) s ⟨s.store, Heap.write s.heap (a.eval s.store) (e.eval s.store)⟩\n  | free {s a v} (hl : s.heap (a.eval s.store) = some v) :\n      Exec (.free a) s ⟨s.store, Heap.erase s.heap (a.eval s.store)⟩\n  | alloc {s x e l} (hfresh : s.heap l = none) :\n      Exec (.alloc x e) s ⟨Store.set s.store x l, Heap.write s.heap l (e.eval s.store)⟩\n  | seq {s s' s'' c₁ c₂} (h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'') :\n      Exec (.seq c₁ c₂) s s''\n  | iteTrue {s s' b c₁ c₂} (hb : b.eval s.store = true) (h : Exec c₁ s s') :\n      Exec (.ite b c₁ c₂) s s'\n  | iteFalse {s s' b c₁ c₂} (hb : b.eval s.store = false) (h : Exec c₂ s s') :\n      Exec (.ite b c₁ c₂) s s'\n  | loopFalse {s b c} (hb : b.eval s.store = false) :\n      Exec (.loop b c) s s\n  | loopTrue {s s' s'' b c} (hb : b.eval s.store = true)\n      (hbody : Exec c s s') (hrest : Exec (.loop b c) s' s'') :\n      Exec (.loop b c) s s''",
          "tag": "illustration",
          "cap": "Ten constructors copied from M5, three addresses turned into <code>Atom</code>s, one new rule."
        },
        {
          "t": "p",
          "h": "And the disproof of determinism:"
        },
        {
          "t": "code",
          "src": "theorem alloc_nondeterministic (x : Var) :\n    ¬ ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂ := by\n  intro hdet\n  have h : (⟨Store.set (fun _ => 0) x 0, Heap.write Heap.empty 0 0⟩ : State)\n         = ⟨Store.set (fun _ => 0) x 1, Heap.write Heap.empty 1 0⟩ :=\n    hdet (.alloc x (.const 0)) ⟨fun _ => 0, Heap.empty⟩ _ _\n      (Exec.alloc (l := 0) rfl) (Exec.alloc (l := 1) rfl)\n  have h01 := congrArg (fun s => s.store x) h\n  simp [Store.set] at h01",
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "alloc_nondeterministic, tactic by tactic",
          "start": "x : Var\n⊢ ¬∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂",
          "steps": [
            {
              "tac": "intro hdet",
              "state": "x : Var\nhdet : ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂\n⊢ False",
              "h": "Note that Lean prints <code>¬∀</code> with no space, and that after <code>intro</code> the goal really is <code>False</code> — negation is not a primitive."
            },
            {
              "tac": "have h : … := hdet … (Exec.alloc (l := 0) rfl) (Exec.alloc (l := 1) rfl)",
              "state": "x : Var\nhdet : ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂\nh :\n  { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 0 } =\n    { store := Store.set (fun x => 0) x 1, heap := Heap.empty.write 1 0 }\n⊢ False",
              "h": "This is the whole theorem, visible: one command, one starting state, two different final states. <code>Heap.empty.write 0 0</code> is Lean's dot notation for <code>Heap.write Heap.empty 0 0</code> — the pretty-printer reorders the first argument even though the source does not."
            },
            {
              "tac": "have h01 := congrArg (fun s => s.store x) h",
              "state": "x : Var\nhdet : ∀ (c : Cmd) (s s₁ s₂ : State), Exec c s s₁ → Exec c s s₂ → s₁ = s₂\nh :\n  { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 0 } =\n    { store := Store.set (fun x => 0) x 1, heap := Heap.empty.write 1 0 }\nh01 :\n  { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 0 }.store x =\n    { store := Store.set (fun x => 0) x 1, heap := Heap.empty.write 1 0 }.store x\n⊢ False",
              "h": "Lean has <i>not</i> reduced <code>{ … }.store</code> — a projection out of a literal structure is left standing by the pretty-printer, and this is the single most common reason a goal in this chapter looks worse than it is. Drop the type ascription on <code>h</code> and it gets worse still: the state literals themselves come back unreduced, so <code>h</code> is displayed as eight lines of <code>{ store := { store := fun x => 0, heap := Heap.empty }.store.set x 0, … }</code>."
            },
            {
              "tac": "simp [Store.set] at h01",
              "state": "No goals.",
              "h": "<code>simp</code> does perform the projection, unfolds <code>Store.set</code>, and lands on <code>0 = 1</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why a new namespace instead of editing Cmd",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "An <code>inductive</code> in Lean is generated once, with a fixed list of constructors, a recursor and a no-confusion principle. There is no <code>extend</code>. In your own copy of the development you would simply edit the M5 definition and let the later files break — that <i>is</i> the exercise. Here, because the workbook has to keep M0–M13 compiling in the same file, the new language is declared inside <code>namespace M14</code>."
            },
            {
              "t": "p",
              "h": "Inside the namespace, <code>Cmd</code> means <code>M14.Cmd</code> and <code>_root_.Cmd</code> means the old one. Everything that does not mention commands — <code>Heap</code>, <code>Assertion</code>, <code>∗</code>, <code>emp</code>, <code>↦</code>, all of Phase 1 — is inherited unchanged, which is a decent practical demonstration of the claim in M2 that the heap algebra is independent of the programming language."
            },
            {
              "t": "p",
              "h": "One casualty: the <code>;;</code> notation is bound to <code>_root_.Cmd.seq</code>, so the snippets below write <code>.seq</code> explicitly."
            }
          ]
        }
      ],
      "pitfall": "<code>Exec.alloc rfl</code> on its own fails. Try <code>refine ⟨_, Exec.alloc rfl⟩</code> against a <code>Safe</code> goal and you get three errors at once, one per unknown: “don't know how to synthesize implicit argument <code>l</code>” with <code>⊢ Val</code>; “don't know how to synthesize implicit argument <code>a</code>” with <code>⊢ Option Val</code>, which is <code>rfl</code>'s own implicit — Lean cannot tell you <i>what</i> is equal to <i>what</i>; and “don't know how to synthesize placeholder for argument <code>w</code>” with <code>⊢ State</code>, which is the <code>_</code> you wrote for the final state. Lean infers implicits from the expected type, and the expected type here is <code>Safe c s</code>, an existential whose witness is itself a metavariable — so there is nothing to infer from and the three unknowns hold each other up. Naming one breaks the deadlock: write <code>Exec.alloc (l := 0) rfl</code> and the other two fall out. The same problem bites for <code>Exec.load</code> and <code>Exec.free</code>, whose value argument <code>v</code> is implicit and determined only by the lookup proof you are leaving as a hole: supply <code>(v := w)</code>.",
      "variants": "Constrain the choice and you get determinism back. Add <code>(hleast : ∀ k, k &lt; l → s.heap k ≠ none)</code> to the constructor and <code>exec_deterministic</code> is provable again: invert both runs, take <code>Nat.lt_trichotomy l₁ l₂</code>, and in each of the two strict branches one run's <code>hleast</code> contradicts the other's <code>hfresh</code>, so <code>l₁ = l₂</code> and the two final states are <code>rfl</code>. Nothing else in the semantics needs touching, since every other constructor was already a function of its input. And the frame rule dies immediately, because the least free location of <code>h</code> and the least free location of <code>h ∪ hFrame</code> need not be the same location. That is the trade in its sharpest form: determinism and locality are not both available. Real allocators <i>are</i> deterministic; separation logic keeps the frame rule anyway by refusing to expose that determinism — the returned pointer is existentially quantified, and the allocator's state never appears in an assertion."
    },
    {
      "t": "ex",
      "id": "m14-2",
      "name": "small-footprint alloc rule",
      "hard": false,
      "why": "Prove the triple above from the semantics. The lesson is not the proof — twelve lines, and nine of them are plumbing — but the two obligations it splits into, and the fact that the existential in the postcondition is not a stylistic choice but the only thing the second obligation will let you write.",
      "setup": "Adopt the demonic definition of <code>Hoare</code> (<code>Safe</code> and <code>∀ s'</code>). Then state the small-footprint rule for allocation and prove it. Before you start, prove the small heap lemma <code>Heap.write Heap.empty l v = Heap.singleton l v</code>: allocation produces its cell with <code>write</code>, but <code>↦</code> is defined with <code>singleton</code>, and nothing in the library bridges the two yet.",
      "hints": [
        "Write the demonic definition down first. Two conjuncts: the command is not stuck, and every run lands in <code>Q</code>. Then look at the postcondition you were going to write and ask which conjunct forbids naming the location.",
        "The safety half is trivial on <code>emp</code>: in the empty heap every location is free, so any witness will do. <code>⟨_, Exec.alloc (l := 0) rfl⟩</code>.",
        "For the correctness half, <code>intro s' hex</code> and then <code>cases hex</code>. Inversion introduces the location the allocator chose as a fresh variable — name it with the pattern <code>| @alloc _ _ _ l hfresh =></code> — and that variable is the witness you feed to <code>aExists</code>.",
        "The remaining goal is a <code>∗</code>, so supply the six-tuple <code>⟨h₁, h₂, hd, hu, hP, hQ⟩</code> exactly as in M4, splitting the heap as <code>Heap.empty ∪ Heap.singleton l v</code>. The <code>pure</code> conjunct is <code>⟨_, rfl⟩</code>: a fact plus <code>emp</code>."
      ],
      "expl": "The precondition is <code>emp</code> and the postcondition owns exactly one cell: this is the smallest possible footprint, which is what makes the rule composable. The existential is forced by the <code>∀ s'</code> obligation — you must satisfy the postcondition for the location the allocator chose, not for one you chose — and the <code>pure</code> conjunct is what lets the caller connect that location to the variable <code>x</code> afterwards.",
      "walk": [
        {
          "tac": "intro σ h hpre",
          "h": "Unfolds <code>Hoare</code> one step: fix a store, a heap, and a proof of the precondition. The goal becomes the conjunction <code>Safe … ∧ ∀ s' …</code>."
        },
        {
          "tac": "obtain ⟨hv, he⟩ := hpre",
          "h": "The precondition is <code>aAnd (fact …) emp</code>, which is a plain conjunction of two assertions at the same heap. <code>obtain</code> splits it: <code>hv</code> pins the value, <code>he : h = Heap.empty</code> pins the heap."
        },
        {
          "tac": "subst he",
          "h": "<code>emp</code> unfolds to <code>h = Heap.empty</code>, so <code>he</code> is an equation with a variable on the left and <code>subst</code> can eliminate <code>h</code> everywhere. After this the goal talks about <code>Heap.empty</code> literally, which is what makes the freshness proof <code>rfl</code>."
        },
        {
          "tac": "refine ⟨⟨_, Exec.alloc (l := 0) rfl⟩, ?_⟩",
          "h": "Discharges the safety obligation and leaves the correctness one. The outer <code>⟨_, _⟩</code> is the conjunction; the inner one is the existential inside <code>Safe</code>. The final state is <code>_</code> because <code>Exec.alloc</code> determines it."
        },
        {
          "tac": "intro s' hex",
          "h": "Now the universal half. <code>s'</code> is <i>any</i> final state and <code>hex</code> is the derivation that produced it. You are no longer allowed to choose."
        },
        {
          "tac": "cases hex with",
          "h": "Inversion. Only one constructor can have produced an execution of <code>.alloc x e</code>, so there is a single branch — but that branch comes with the allocator's choice as a new variable."
        },
        {
          "tac": "| @alloc _ _ _ l hfresh =>",
          "h": "The <code>@</code> form lets you name implicit arguments positionally. The three underscores are <code>s</code>, <code>x</code>, <code>e</code>, which are already determined; <code>l</code> is the one you want a name for. Without the <code>@</code> pattern Lean would introduce it as an inaccessible name and you could not write the witness."
        },
        {
          "tac": "refine ⟨l, Heap.empty, Heap.singleton l v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩",
          "h": "Seven components in one anonymous constructor: the existential witness <code>l</code>, then the M4 star tuple (left heap, right heap, disjointness, the union equation, the <code>pure</code> proof, the <code>↦</code> proof). The <code>pure</code> proof is itself a pair — a fact and an <code>emp</code> — hence the nested <code>⟨?_, rfl⟩</code>."
        },
        {
          "tac": "· show Heap.write Heap.empty l (e.eval σ) = Heap.union Heap.empty (Heap.singleton l v)",
          "h": "<code>show</code> restates the goal in a definitionally equal but readable form. Lean was displaying the left-hand side as a projection out of an anonymous state literal; this is the same term with the projection performed."
        },
        {
          "tac": "  rw [union_empty_left, write_empty, show e.eval σ = v from hv]",
          "h": "Three rewrites, left to right: kill the union with <code>emp</code>, turn <code>write</code> on the empty heap into <code>singleton</code>, and replace the evaluated expression by the value the precondition pinned. The inline <code>show … from hv</code> is how you use <code>hv</code> as a rewrite rule when its type is stated through <code>fact</code>."
        },
        {
          "tac": "· show Store.set σ x l x = l",
          "h": "The remaining <code>pure</code> fact: the variable now holds the location."
        },
        {
          "tac": "  simp [Store.set]",
          "h": "Unfolds the update and evaluates <code>if x = x</code>."
        }
      ],
      "deep": [
        {
          "t": "p",
          "h": "The heap lemma first — without it every alloc proof stalls at the point where a <code>write</code> has to become a <code>↦</code>:"
        },
        {
          "t": "code",
          "src": "theorem write_empty (l : Loc) (v : Val) :\n    Heap.write Heap.empty l v = Heap.singleton l v := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, Heap.empty, Heap.singleton, hx]",
          "tag": "illustration"
        },
        {
          "t": "p",
          "h": "Three tactics, and the third does both branches at once — that is what <code>&lt;;&gt;</code> is for: it runs the tactic on the right against every goal the tactic on the left produced. Unfolding <code>Heap.write</code> and <code>Heap.singleton</code> leaves an <code>if x = l</code> on each side of the equation. In the <code>pos</code> branch <code>hx : x = l</code> is in the simp set, so both tests reduce to true and the goal becomes <code>some v = some v</code>; in the <code>neg</code> branch both reduce to false, <code>Heap.empty</code> unfolds, and the goal becomes <code>none = none</code>. The <code>funext x</code> at the top is there for the usual reason: <code>Heap</code> is a function type, two heaps are equal exactly when they agree at every location, and Lean will not take that step unasked."
        },
        {
          "t": "p",
          "h": "The demonic triple and the rule:"
        },
        {
          "t": "code",
          "src": "def Safe (c : Cmd) (s : State) : Prop := ∃ s', Exec c s s'\n\ndef Hoare (P : Assertion) (c : Cmd) (Q : Assertion) : Prop :=\n  ∀ σ h, P σ h →\n    Safe c ⟨σ, h⟩ ∧ ∀ s', Exec c ⟨σ, h⟩ s' → Q s'.store s'.heap",
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": "theorem hoare_alloc (x : Var) (e : Atom) (v : Val) :\n    Hoare (aAnd (fact (fun σ => e.eval σ = v)) emp) (.alloc x e)\n      (aExists fun l => pure (fun σ => σ x = l) ∗ (l ↦ v)) := by\n  intro σ h hpre\n  obtain ⟨hv, he⟩ := hpre\n  subst he\n  refine ⟨⟨_, Exec.alloc (l := 0) rfl⟩, ?_⟩\n  intro s' hex\n  cases hex with\n  | @alloc _ _ _ l hfresh =>\n      refine ⟨l, Heap.empty, Heap.singleton l v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩\n      · show Heap.write Heap.empty l (e.eval σ) = Heap.union Heap.empty (Heap.singleton l v)\n        rw [union_empty_left, write_empty, show e.eval σ = v from hv]\n      · show Store.set σ x l x = l\n        simp [Store.set]",
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "hoare_alloc, tactic by tactic",
          "start": "x : Var\ne : Atom\nv : Val\n⊢ Hoare (aAnd (fact fun σ => Atom.eval σ e = v) emp) (Cmd.alloc x e)\n    (aExists fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v)",
          "steps": [
            {
              "tac": "intro σ h hpre",
              "state": "x : Var\ne : Atom\nv : Val\nσ : Store\nh : Heap\nhpre : aAnd (fact fun σ => Atom.eval σ e = v) emp σ h\n⊢ Safe (Cmd.alloc x e) { store := σ, heap := h } ∧\n    ∀ (s' : State),\n      Exec (Cmd.alloc x e) { store := σ, heap := h } s' →\n        aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap",
              "h": "There are the two obligations, side by side. Lean prints <code>_root_.pure</code> because <code>pure</code> is also the name of a method of the <code>Pure</code> class; the workbook's <code>pure</code> is the one at the root namespace."
            },
            {
              "tac": "obtain ⟨hv, he⟩ := hpre",
              "state": "x : Var\ne : Atom\nv : Val\nσ : Store\nh : Heap\nhv : fact (fun σ => Atom.eval σ e = v) σ h\nhe : emp σ h\n⊢ Safe (Cmd.alloc x e) { store := σ, heap := h } ∧\n    ∀ (s' : State),\n      Exec (Cmd.alloc x e) { store := σ, heap := h } s' →\n        aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap",
              "h": "Note that <code>he</code> is displayed as <code>emp σ h</code>, not as <code>h = Heap.empty</code>. It is the same proposition; <code>subst</code> sees through the definition."
            },
            {
              "tac": "subst he",
              "state": "x : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\n⊢ Safe (Cmd.alloc x e) { store := σ, heap := Heap.empty } ∧\n    ∀ (s' : State),\n      Exec (Cmd.alloc x e) { store := σ, heap := Heap.empty } s' →\n        aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap",
              "h": "<code>h</code> is gone from the context entirely. Everything now mentions <code>Heap.empty</code>, which is why <code>rfl</code> will prove freshness."
            },
            {
              "tac": "refine ⟨⟨_, Exec.alloc (l := 0) rfl⟩, ?_⟩",
              "state": "x : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\n⊢ ∀ (s' : State),\n    Exec (Cmd.alloc x e) { store := σ, heap := Heap.empty } s' →\n      aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap",
              "h": "Safety is discharged. What is left is exactly <code>PartialHoare</code>."
            },
            {
              "tac": "intro s' hex",
              "state": "x : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\ns' : State\nhex : Exec (Cmd.alloc x e) { store := σ, heap := Heap.empty } s'\n⊢ aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v) s'.store s'.heap",
              "h": "<code>s'</code> is universally quantified. This is the moment the existential in the postcondition becomes unavoidable: you have no idea which location is in <code>s'</code>."
            },
            {
              "tac": "cases hex with | @alloc _ _ _ l hfresh =>",
              "state": "case alloc\nx : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\nl : Val\nhfresh : { store := σ, heap := Heap.empty }.heap l = none\n⊢ aExists (fun l => (_root_.pure fun σ => σ x = l) ∗ l ↦ v)\n    { store := { store := σ, heap := Heap.empty }.store.set x l,\n        heap :=\n          { store := σ, heap := Heap.empty }.heap.write l (Atom.eval { store := σ, heap := Heap.empty }.store e) }.store\n    { store := { store := σ, heap := Heap.empty }.store.set x l,\n        heap :=\n          { store := σ, heap := Heap.empty }.heap.write l (Atom.eval { store := σ, heap := Heap.empty }.store e) }.heap",
              "h": "There is <code>l</code>, the allocator's choice, produced by inversion. Lean displays it at type <code>Val</code>, not <code>Loc</code>, even though it is being used as an address — <code>Loc</code> and <code>Val</code> are both <code>abbrev</code>s for <code>Nat</code>, and an <code>abbrev</code> is reducible, so the two are the same type and the display is free to print either name. Nothing turns on it and there is no coercion to hunt for. The goal is unreadable for one reason only: <code>{ store := … }.store</code> has not been reduced."
            },
            {
              "tac": "refine ⟨l, Heap.empty, Heap.singleton l v, disjoint_empty_left _, ?_, ⟨?_, rfl⟩, rfl⟩",
              "state": "case alloc.refine_1\nx : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\nl : Val\nhfresh : { store := σ, heap := Heap.empty }.heap l = none\n⊢ { store := { store := σ, heap := Heap.empty }.store.set x l,\n        heap :=\n          { store := σ, heap := Heap.empty }.heap.write l\n            (Atom.eval { store := σ, heap := Heap.empty }.store e) }.heap =\n    Heap.empty.union (Heap.singleton l v)",
              "h": "Two goals remain, both small. This is the union equation; the second, shown three steps down, is the <code>pure</code> fact. Four of the seven components went in without leaving a hole: <code>l</code>, the two heaps, and <code>disjoint_empty_left _</code>."
            },
            {
              "tac": "show Heap.write Heap.empty l (e.eval σ) = Heap.union Heap.empty (Heap.singleton l v)",
              "state": "case alloc.refine_1\nx : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\nl : Val\nhfresh : { store := σ, heap := Heap.empty }.heap l = none\n⊢ Heap.empty.write l (Atom.eval σ e) = Heap.empty.union (Heap.singleton l v)",
              "h": "Same proposition, one line instead of five. <code>show</code> is the correct tool whenever inversion has left you staring at record projections: it type-checks the term you wrote against the goal up to definitional unfolding, and record projection out of a record literal is a definitional step, so it always succeeds here — it just never happens on its own."
            },
            {
              "tac": "rw [union_empty_left, write_empty, show e.eval σ = v from hv]",
              "state": "case alloc.refine_2\nx : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\nl : Val\nhfresh : { store := σ, heap := Heap.empty }.heap l = none\n⊢ fact (fun σ => σ x = l)\n    { store := { store := σ, heap := Heap.empty }.store.set x l,\n        heap :=\n          { store := σ, heap := Heap.empty }.heap.write l (Atom.eval { store := σ, heap := Heap.empty }.store e) }.store\n    Heap.empty",
              "h": "First goal closed. The second is the <code>pure</code> fact, and it arrives in the same projected shape as everything else — <code>fact</code> applied to a store that is still written as <code>{ … }.store</code>. Note also that <code>fact φ σ h</code> ignores its heap argument, which is why <code>Heap.empty</code> is sitting there doing nothing."
            },
            {
              "tac": "show Store.set σ x l x = l",
              "state": "case alloc.refine_2\nx : Var\ne : Atom\nv : Val\nσ : Store\nhv : fact (fun σ => Atom.eval σ e = v) σ Heap.empty\nl : Val\nhfresh : { store := σ, heap := Heap.empty }.heap l = none\n⊢ σ.set x l x = l",
              "h": "The second <code>show</code>. It unfolds <code>fact</code>, performs the projection, and drops the irrelevant heap argument, all by definitional equality — three reductions that no tactic was asked to perform, because <code>show</code> only has to check that the type you wrote and the type Lean has are the same term after unfolding."
            },
            {
              "tac": "simp [Store.set]",
              "state": "No goals.",
              "h": "<code>Store.set σ x l</code> is <code>fun y => if y = x then l else σ y</code>, so at <code>y = x</code> the test is the decidable proposition <code>x = x</code>. Ask <code>simp?</code> what it used and it answers <code>simp only [Store.set, ↓reduceIte]</code>: not <code>if_pos</code>, but the simproc that evaluates an <code>if</code> whose condition has a closed decidability proof."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "The value in the postcondition, and why the sketch at the top is wrong",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The sketch in “Option A” writes the postcondition as <code>aExists fun l => pure (fun σ => σ x = l) ∗ (l ↦ e.eval σ)</code>. Look at the two <code>σ</code>s. The inner <code>fun σ</code> binds only the body of <code>pure</code>; the <code>σ</code> in <code>e.eval σ</code> is bound by nothing at all. Type the sketch into Lean and it is accepted anyway, because auto-bound implicits quietly close it up for you — <code>#check</code> then reports the statement as <code>∀ {x : Var} {e : Atom} {σ : Store}, Hoare emp (Cmd.alloc x e) …</code>. That <code>σ</code> is fixed before the command runs and has no relation to the execution, so the postcondition is claiming something about the new cell computed in a store nobody was in."
            },
            {
              "t": "p",
              "h": "Bind it the way you meant to — make <code>σ</code> the assertion's own store argument — and it is still wrong, now for a reason about the language rather than about Lean. An assertion is a function of the <i>final</i> store, so <code>e.eval σ</code> now means “evaluate <code>e</code> after the allocation”. But allocation writes <code>x</code>. Take <code>e = .var x</code>: the specification asks for a cell holding the final value of <code>x</code>, which is the location; the semantics wrote <code>e.eval s.store</code> with <code>s</code> the state <i>before</i> the update, which is the old <code>σ x</code>. Run <code>alloc x (.var x)</code> from the everywhere-zero store and let the allocator choose location <code>1</code>: the heap ends as <code>1 ↦ 0</code> and the postcondition demands <code>1 ↦ 1</code>. So the triple is not merely unprovable — it is false, and the demonic reading is what lets you say so."
            },
            {
              "t": "p",
              "h": "The repair used above is the same one M9 used for <code>hoare_write_val</code>: pin the value with a pure side condition in the precondition, so that the postcondition mentions a <code>Val</code> and never re-evaluates an expression. That is why the statement carries <code>aAnd (fact (fun σ => e.eval σ = v)) emp</code> rather than plain <code>emp</code>. The alternative repair — add a <code>subst</code>-style store operator to the assertion language — is what real developments do, and it costs a chapter."
            },
            {
              "t": "code",
              "src": "theorem hoare_write_val (l : Loc) (e : Atom) (old v : Val) :\n    Hoare (aAnd (fact (fun σ => e.eval σ = v)) (l ↦ old)) (.write l e) (l ↦ v)",
              "tag": "verified",
              "cap": "M9's rule, for comparison: the same trick, five chapters earlier."
            }
          ]
        }
      ],
      "pitfall": "Trying to prove the triple with the location named — postcondition <code>pure (fun σ => σ x = 0) ∗ (0 ↦ v)</code> — and finding that it <i>works</i>. It works under the angelic definition, and the fact that it works is the bug. If your alloc rule went through without you ever writing <code>aExists</code>, check which definition of <code>Hoare</code> you are using before you celebrate.",
      "variants": "Drop the existential and the theorem is false demonically: fix the location to <code>0</code>, take the run in which the allocator picks <code>1</code>, and the postcondition fails. Drop the <code>fact</code> guard on the value and the statement becomes the sketch discussed above — provable only when <code>e</code> does not mention <code>x</code>, which is a side condition you would then have to carry everywhere. Strengthen the precondition from <code>emp</code> to <code>l₀ ↦ u</code> and the rule survives, but neither for free nor unchanged. The postcondition has to grow the same cell back — <code>aExists fun l => (pure (fun σ => σ x = l) ∗ (l ↦ v)) ∗ (l₀ ↦ u)</code> — and to build that star you must first derive <code>l ≠ l₀</code>, which comes out of <code>hfresh</code>: if <code>l</code> were <code>l₀</code>, then <code>Heap.singleton l₀ u l = none</code> contradicts <code>singleton_same</code>. Safety stops being free too, because <code>l₀</code> may be <code>0</code>: you exhibit <code>l₀ + 1</code> and discharge freshness with <code>singleton_other</code>. All of that goes through. All of it is also the frame rule being re-derived by hand for one particular frame — which is the failure mode the reference chapter warns about."
    },
    {
      "t": "ex",
      "id": "m14-3",
      "name": "locality of alloc under framing",
      "hard": false,
      "why": "Prove <code>HeapLocal (.alloc x e)</code> — this is where the existential earns its keep. It earns it by failing. <code>HeapLocal</code> as stated in M8 is <b>false</b> for allocation: attempt it, watch the first conjunct refuse to close, build the two-cell counterexample, and then find the condition that does survive. That sequence is the exercise.",
      "setup": "Start by trying to prove <code>HeapLocal (.alloc x e)</code> directly. When the first conjunct refuses to close, build the counterexample. Then state the <b>frame property</b> — the same relation with the quantification reversed — and prove <i>that</i> for allocation. Finally, prove the demonic frame rule from the frame property plus safety monotonicity plus <code>Preserves</code>, and notice which of the three hypotheses <code>alloc</code> does not satisfy.",
      "hints": [
        "Read the first conjunct of <code>HeapLocal</code> on its own: <code>Heap.disjoint s'.heap hFrame</code>. The small run produced <code>s'</code>. What did it put in the heap, and what stopped it from putting it where the frame already is?",
        "Counterexample: <code>h = Heap.empty</code>, <code>hFrame = Heap.singleton 0 w</code>. They are disjoint. Now run <code>alloc</code> on the empty heap and let it choose location <code>0</code>. Instantiate <code>hloc</code> at exactly that and look at what you get.",
        "For the repair, swap which run you are given and which you must produce. If the <i>big</i> run chose <code>l</code>, then <code>Heap.union h hFrame l = none</code>, and <code>union_eq_none</code> splits that into <code>h l = none</code> and <code>hFrame l = none</code> — the first lets the small heap make the same choice, the second gives you disjointness for free.",
        "The heap equation you need is <code>Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame</code>, and you have seen it: it is M8's <code>write_union_no_disjointness</code>. That one was an illustration in M8's text rather than a corpus theorem, so you will have to restate it. The shape is <code>funext x</code>, <code>by_cases hxl : x = l</code>, and in the negative branch <code>cases hx : h x</code> — the colon form, which splits on the two constructors of <code>Option Val</code> <i>and</i> records the equation under the name <code>hx</code>, which is what <code>union_of_none</code> / <code>union_of_some</code> need as an argument.",
        "When you instantiate <code>hfresh</code>, Lean hands it to you as <code>{ store := σ, heap := h.union hFrame }.heap l = none</code>. Restate it: <code>have hfresh' : Heap.union h hFrame l = none := hfresh</code>."
      ],
      "expl": "Locality is two conditions, not one, and M8 could get away with conflating them because none of its commands could fail on a bigger heap or behave differently on one. Allocation separates them. It has the frame property (every big run projects to a small run) and lacks safety monotonicity (a run on the small heap need not survive to the big one), and those two facts are exactly the content of “allocation is local, but only over finite heaps”.",
      "walk": [
        {
          "tac": "intro σ h hFrame r hd hex",
          "h": "Six binders, matching the six arguments of <code>FrameProperty</code>. Note <code>r</code>: this is the run on the <i>big</i> heap, and it is given to you. In <code>HeapLocal</code> the given run was on the small heap."
        },
        {
          "tac": "cases hex with",
          "h": "Invert the big run. One branch, since only <code>Exec.alloc</code> can produce it."
        },
        {
          "tac": "| @alloc _ _ _ l hfresh =>",
          "h": "<code>l</code> is the location the big run chose, and <code>hfresh</code> says it was free in <code>h ∪ hFrame</code>. Everything below is squeezing those two facts."
        },
        {
          "tac": "have hfresh' : Heap.union h hFrame l = none := hfresh",
          "h": "A restatement. Inversion handed you <code>hfresh</code> at the type <code>{ store := σ, heap := h.union hFrame }.heap l = none</code>; this is the same proof term at the type you can read. Lean accepts <code>:= hfresh</code> because the two types are definitionally equal — performing the projection is a reduction, not a proof step. Strictly this line is optional here: <code>union_eq_none.mp hfresh</code> also elaborates, because unification unfolds the projection on its own. It stops being optional the moment you want to <code>rw</code>; see the pitfall."
        },
        {
          "tac": "obtain ⟨hh, hf⟩ := union_eq_none.mp hfresh'",
          "h": "The heart of the proof. Freshness in the union is freshness in <i>both</i> parts. <code>hh : h l = none</code> lets the small heap replay the same choice; <code>hf : hFrame l = none</code> is what makes the result disjoint from the frame. In the small-to-big direction you would need to <i>conclude</i> <code>hf</code>, and there is no way to."
        },
        {
          "tac": "refine ⟨⟨Store.set σ x l, Heap.write h l (e.eval σ)⟩, Exec.alloc hh, ?_, rfl, ?_⟩",
          "h": "Supply the small run explicitly — same variable, same location, same value — and the store equation falls out as <code>rfl</code> because allocation does not consult the heap when updating the store."
        },
        {
          "tac": "· intro y",
          "h": "First hole: disjointness of the small result from the frame. <code>Heap.disjoint</code> unfolds to a <code>∀ l</code>, so <code>intro</code> works directly on it."
        },
        {
          "tac": "  by_cases hyl : y = l",
          "h": "Two cases, and they are answered by the two halves of <code>union_eq_none</code>."
        },
        {
          "tac": "  · subst hyl; exact Or.inr hf",
          "h": "At the new cell: the frame does not own it, by <code>hf</code>. This is the case that is unprovable in the other direction."
        },
        {
          "tac": "  · rcases hd y with hy | hy",
          "h": "Away from the new cell nothing changed, so the old disjointness <code>hd</code> answers it. <code>rcases</code> splits the disjunction."
        },
        {
          "tac": "    · left; show Heap.write h l (e.eval σ) y = none",
          "h": "<code>show</code> again, for the same reason as before: the goal is stated through a state projection and <code>write_other</code> will not match it."
        },
        {
          "tac": "      rw [write_other h l y (e.eval σ) hyl]; exact hy",
          "h": "<code>write_other</code> needs <code>y ≠ l</code>, which is exactly the negative <code>by_cases</code> branch."
        },
        {
          "tac": "    · exact Or.inr hy",
          "h": "The frame was already free at <code>y</code>."
        },
        {
          "tac": "· exact write_union h hFrame l (e.eval σ)",
          "h": "Second hole: the heap equation, which is the standalone lemma. Note that it needs no hypotheses — writing a cell into a union is the same as writing it into the left part, whatever the two heaps are."
        }
      ],
      "deep": [
        {
          "t": "p",
          "h": "First, the theorem that ought to be true and is not:"
        },
        {
          "t": "code",
          "src": "def HeapLocal (c : Cmd) : Prop :=\n  ∀ σ h hFrame s',\n    Heap.disjoint h hFrame →\n    Exec c ⟨σ, h⟩ s' →\n    Heap.disjoint s'.heap hFrame ∧\n    ∃ r : State,\n      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧\n      r.store = s'.store ∧\n      r.heap = Heap.union s'.heap hFrame",
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": "theorem alloc_not_heapLocal (x : Var) (v w : Val) :\n    ¬ HeapLocal (.alloc x (.const v)) := by\n  intro hloc\n  obtain ⟨hdEnd, -⟩ :=\n    hloc (fun _ => 0) Heap.empty (Heap.singleton 0 w)\n      ⟨Store.set (fun _ => 0) x 0, Heap.write Heap.empty 0 v⟩\n      (disjoint_empty_left _) (Exec.alloc (l := 0) rfl)\n  rcases hdEnd 0 with h0 | h0\n  · have h0' : Heap.write Heap.empty 0 v 0 = none := h0\n    rw [write_same] at h0'\n    exact absurd h0' (by simp)\n  · rw [singleton_same] at h0\n    exact absurd h0 (by simp)",
          "tag": "illustration",
          "cap": "Small heap empty, frame owning cell 0, allocator picks cell 0."
        },
        {
          "t": "trace",
          "title": "alloc_not_heapLocal, tactic by tactic",
          "start": "x : Var\nv w : Val\n⊢ ¬HeapLocal (Cmd.alloc x (Atom.const v))",
          "steps": [
            {
              "tac": "intro hloc",
              "state": "x : Var\nv w : Val\nhloc : HeapLocal (Cmd.alloc x (Atom.const v))\n⊢ False",
              "h": "Assume locality and derive a contradiction."
            },
            {
              "tac": "obtain ⟨hdEnd, -⟩ := hloc (fun _ => 0) Heap.empty (Heap.singleton 0 w) …",
              "state": "x : Var\nv w : Val\nhloc : HeapLocal (Cmd.alloc x (Atom.const v))\nhdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)\n⊢ False",
              "h": "The <code>-</code> in the pattern <i>discards</i> the second component — the existential over the big run — because the contradiction is already in the first. <code>hdEnd</code> claims that a heap holding cell <code>0</code> is disjoint from a heap holding cell <code>0</code>."
            },
            {
              "tac": "rcases hdEnd 0 with h0 | h0",
              "state": "case inl\nx : Var\nv w : Val\nhloc : HeapLocal (Cmd.alloc x (Atom.const v))\nhdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)\nh0 : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap 0 = none\n⊢ False",
              "h": "<code>Heap.disjoint h₁ h₂</code> is <code>∀ l, h₁ l = none ∨ h₂ l = none</code>, so <code>hdEnd 0</code> is a disjunction and <code>rcases … with h0 | h0</code> splits it into the two cases Lean names <code>inl</code> and <code>inr</code>. Both are absurd."
            },
            {
              "tac": "· have h0' : Heap.write Heap.empty 0 v 0 = none := h0",
              "state": "case inl\nx : Var\nv w : Val\nhloc : HeapLocal (Cmd.alloc x (Atom.const v))\nhdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)\nh0 : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap 0 = none\nh0' : Heap.empty.write 0 v 0 = none\n⊢ False",
              "h": "Restate through the projection so that <code>write_same</code> matches. Note that you write <code>Heap.write Heap.empty 0 v 0</code> and Lean displays <code>Heap.empty.write 0 v 0</code>: the pretty-printer moves the first explicit argument in front of the dot whenever its type matches the namespace. The two spellings are the same term."
            },
            {
              "tac": "  rw [write_same] at h0'; exact absurd h0' (by simp)",
              "state": "case inr\nx : Var\nv w : Val\nhloc : HeapLocal (Cmd.alloc x (Atom.const v))\nhdEnd : { store := Store.set (fun x => 0) x 0, heap := Heap.empty.write 0 v }.heap.disjoint (Heap.singleton 0 w)\nh0 : Heap.singleton 0 w 0 = none\n⊢ False",
              "h": "<code>write_same</code> turns <code>h0'</code> into <code>some v = none</code>; <code>absurd hyp proof-of-negation</code> then produces a term of any type, here <code>False</code>, and the <code>by simp</code> is what proves <code>¬(some v = none)</code> by constructor disjointness. Second branch is the mirror image with <code>singleton_same</code>."
            },
            {
              "tac": "· rw [singleton_same] at h0; exact absurd h0 (by simp)",
              "state": "No goals.",
              "h": ""
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "Now the condition that survives. It is the same relation with the two runs swapped:"
        },
        {
          "t": "code",
          "src": "def FrameProperty (c : Cmd) : Prop :=\n  ∀ σ h hFrame r,\n    Heap.disjoint h hFrame →\n    Exec c ⟨σ, Heap.union h hFrame⟩ r →\n    ∃ s' : State,\n      Exec c ⟨σ, h⟩ s' ∧\n      Heap.disjoint s'.heap hFrame ∧\n      r.store = s'.store ∧\n      r.heap = Heap.union s'.heap hFrame",
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": "theorem write_union (h hFrame : Heap) (l : Loc) (v : Val) :\n    Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame := by\n  funext x\n  by_cases hxl : x = l\n  · subst hxl\n    rw [write_same, union_of_some hFrame (write_same h x v)]\n  · rw [write_other _ l x v hxl]\n    have hwx : Heap.write h l v x = h x := write_other h l x v hxl\n    cases hx : h x with\n    | none   => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]\n    | some u => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]",
          "tag": "illustration",
          "cap": "A pure heap-algebra lemma, no disjointness needed. You have met it: this is M8's <code>write_union_no_disjointness</code>, which was pulled out of the tail of <code>heapLocal_write</code> there. It never became a corpus theorem — in <code>heapLocal_write</code> the argument sits inline after a <code>show</code> — so it is restated here, and renamed, because it is now load-bearing rather than an aside."
        },
        {
          "t": "code",
          "src": "theorem frameProperty_alloc (x : Var) (e : Atom) : FrameProperty (.alloc x e) := by\n  intro σ h hFrame r hd hex\n  cases hex with\n  | @alloc _ _ _ l hfresh =>\n      have hfresh' : Heap.union h hFrame l = none := hfresh\n      obtain ⟨hh, hf⟩ := union_eq_none.mp hfresh'\n      refine ⟨⟨Store.set σ x l, Heap.write h l (e.eval σ)⟩, Exec.alloc hh, ?_, rfl, ?_⟩\n      · intro y\n        by_cases hyl : y = l\n        · subst hyl; exact Or.inr hf\n        · rcases hd y with hy | hy\n          · left\n            show Heap.write h l (e.eval σ) y = none\n            rw [write_other h l y (e.eval σ) hyl]; exact hy\n          · exact Or.inr hy\n      · exact write_union h hFrame l (e.eval σ)",
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "frameProperty_alloc, tactic by tactic",
          "start": "x : Var\ne : Atom\n⊢ FrameProperty (Cmd.alloc x e)",
          "steps": [
            {
              "tac": "intro σ h hFrame r hd hex",
              "state": "x : Var\ne : Atom\nσ : Store\nh hFrame : Heap\nr : State\nhd : h.disjoint hFrame\nhex : Exec (Cmd.alloc x e) { store := σ, heap := h.union hFrame } r\n⊢ ∃ s',\n    Exec (Cmd.alloc x e) { store := σ, heap := h } s' ∧\n      s'.heap.disjoint hFrame ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Compare with <code>HeapLocal</code>: there the hypothesis was the small run and the existential was the big one."
            },
            {
              "tac": "cases hex with | @alloc _ _ _ l hfresh =>",
              "state": "case alloc\nx : Var\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nl : Val\nhfresh : { store := σ, heap := h.union hFrame }.heap l = none\n⊢ ∃ s',\n    Exec (Cmd.alloc x e) { store := σ, heap := h } s' ∧\n      s'.heap.disjoint hFrame ∧\n        { store := { store := σ, heap := h.union hFrame }.store.set x l,\n                heap :=\n                  { store := σ, heap := h.union hFrame }.heap.write l\n                    (Atom.eval { store := σ, heap := h.union hFrame }.store e) }.store =\n            s'.store ∧\n          { store := { store := σ, heap := h.union hFrame }.store.set x l,\n                heap :=\n                  { store := σ, heap := h.union hFrame }.heap.write l\n                    (Atom.eval { store := σ, heap := h.union hFrame }.store e) }.heap =\n            s'.heap.union hFrame",
              "h": "<code>r</code> has been replaced by the state the constructor produces. The location <code>l</code> is the big run's choice."
            },
            {
              "tac": "obtain ⟨hh, hf⟩ := union_eq_none.mp hfresh'",
              "state": "case alloc\nx : Var\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nl : Val\nhfresh : { store := σ, heap := h.union hFrame }.heap l = none\nhfresh' : h.union hFrame l = none\nhh : h l = none\nhf : hFrame l = none\n⊢ ∃ s', …",
              "h": "The goal is untouched — it is still the thirteen-line display printed above, elided here — and the whole mathematical content of the theorem is in the three new lines. Freshness in the union splits: <code>hh</code> licenses the small run, <code>hf</code> gives disjointness at the new cell. <code>union_eq_none</code> is an <code>Iff</code>, so <code>.mp</code> is its forward direction."
            },
            {
              "tac": "refine ⟨⟨Store.set σ x l, Heap.write h l (e.eval σ)⟩, Exec.alloc hh, ?_, rfl, ?_⟩",
              "state": "case alloc.refine_1\nx : Var\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nl : Val\nhfresh : { store := σ, heap := h.union hFrame }.heap l = none\nhfresh' : h.union hFrame l = none\nhh : h l = none\nhf : hFrame l = none\n⊢ { store := σ.set x l, heap := h.write l (Atom.eval σ e) }.heap.disjoint hFrame",
              "h": "The store equation went through as <code>rfl</code>; two goals remain."
            },
            {
              "tac": "· intro y … (the disjointness case split)",
              "state": "case alloc.refine_2\nx : Var\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nl : Val\nhfresh : { store := σ, heap := h.union hFrame }.heap l = none\nhfresh' : h.union hFrame l = none\nhh : h l = none\nhf : hFrame l = none\n⊢ { store := { store := σ, heap := h.union hFrame }.store.set x l,\n        heap :=\n          { store := σ, heap := h.union hFrame }.heap.write l\n            (Atom.eval { store := σ, heap := h.union hFrame }.store e) }.heap =\n    { store := σ.set x l, heap := h.write l (Atom.eval σ e) }.heap.union hFrame",
              "h": "The last goal, once projections are reduced, is precisely <code>write_union</code>."
            },
            {
              "tac": "· exact write_union h hFrame l (e.eval σ)",
              "state": "No goals.",
              "h": ""
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "The payoff. This is M8's frame theorem, restated for the demonic triple, with locality split into its two halves:"
        },
        {
          "t": "code",
          "src": "def Preserves (c : Cmd) (R : Assertion) : Prop :=\n  ∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame\n\ntheorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hfp : FrameProperty c) (hsm : SafetyMonotone c)\n    (hpres : Preserves c R) : Hoare (P ∗ R) c (Q ∗ R) := by\n  intro σ h hstar\n  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar\n  subst hu\n  refine ⟨hsm σ hP hR hd (hc σ hP hp).1, ?_⟩\n  intro r hex\n  obtain ⟨s', hex', hdEnd, hst, hhp⟩ := hfp σ hP hR r hd hex\n  refine ⟨s'.heap, hR, hdEnd, hhp, ?_, ?_⟩\n  · rw [hst]; exact (hc σ hP hp).2 s' hex'\n  · exact hpres ⟨σ, Heap.union hP hR⟩ r hex hR hr",
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "hoare_frame, tactic by tactic",
          "start": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\n⊢ Hoare (P ∗ R) c (Q ∗ R)",
          "steps": [
            {
              "tac": "intro σ h hstar",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\nσ : Store\nh : Heap\nhstar : (P ∗ R) σ h\n⊢ Safe c { store := σ, heap := h } ∧ ∀ (s' : State), Exec c { store := σ, heap := h } s' → (Q ∗ R) s'.store s'.heap",
              "h": "Two obligations, and they will be discharged by two different hypotheses. The six lines above <code>σ</code> are the statement's own binders; Lean reprints them at every step below, so watch only what changes underneath."
            },
            {
              "tac": "obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\n⊢ Safe c { store := σ, heap := h } ∧ ∀ (s' : State), Exec c { store := σ, heap := h } s' → (Q ∗ R) s'.store s'.heap",
              "h": "The M4 six-tuple, unchanged from Phase 1. Nothing about <code>∗</code> had to be revisited for allocation — which is the point of having kept the heap algebra separate from the semantics. Note that Lean has merged <code>h</code>, <code>hP</code> and <code>hR</code> onto one line now that they share a type."
            },
            {
              "tac": "subst hu",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\n⊢ Safe c { store := σ, heap := hP.union hR } ∧\n    ∀ (s' : State), Exec c { store := σ, heap := hP.union hR } s' → (Q ∗ R) s'.store s'.heap",
              "h": "Replace <code>h</code> by the split everywhere. <code>h</code> and <code>hu</code> both leave the context; the goal, now two lines wide, is stated entirely in terms of the two pieces."
            },
            {
              "tac": "refine ⟨hsm σ hP hR hd (hc σ hP hp).1, ?_⟩",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\n⊢ ∀ (s' : State), Exec c { store := σ, heap := hP.union hR } s' → (Q ∗ R) s'.store s'.heap",
              "h": "Safety monotonicity, used once, on the safety half of the small triple: <code>(hc σ hP hp).1</code> is that half — the <code>.1</code> is the first component of the conjunction <code>Hoare</code> now unfolds to. This is the <i>only</i> place <code>hsm</code> appears, and it is why allocation over functional heaps does not get the frame rule."
            },
            {
              "tac": "intro r hex ; obtain ⟨s', hex', hdEnd, hst, hhp⟩ := hfp σ hP hR r hd hex",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\nr : State\nhex : Exec c { store := σ, heap := hP.union hR } r\ns' : State\nhex' : Exec c { store := σ, heap := hP } s'\nhdEnd : s'.heap.disjoint hR\nhst : r.store = s'.store\nhhp : r.heap = s'.heap.union hR\n⊢ (Q ∗ R) r.store r.heap",
              "h": "The frame property, used once, to turn an arbitrary big run <code>hex</code> into a small run <code>hex'</code> plus an untouched frame. Everything below is bookkeeping on the four facts it returned."
            },
            {
              "tac": "refine ⟨s'.heap, hR, hdEnd, hhp, ?_, ?_⟩",
              "state": "case refine_1\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\nr : State\nhex : Exec c { store := σ, heap := hP.union hR } r\ns' : State\nhex' : Exec c { store := σ, heap := hP } s'\nhdEnd : s'.heap.disjoint hR\nhst : r.store = s'.store\nhhp : r.heap = s'.heap.union hR\n⊢ Q r.store s'.heap",
              "h": "Rebuild the star from the pieces the frame property handed over: the two heaps are <code>s'.heap</code> and <code>hR</code>, their disjointness is <code>hdEnd</code>, and the union equation is <code>hhp</code> — which is exactly why the frame property was made to return those four things in that order."
            },
            {
              "tac": "· rw [hst]; exact (hc σ hP hp).2 s' hex'",
              "state": "case refine_2\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhfp : FrameProperty c\nhsm : SafetyMonotone c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\nr : State\nhex : Exec c { store := σ, heap := hP.union hR } r\ns' : State\nhex' : Exec c { store := σ, heap := hP } s'\nhdEnd : s'.heap.disjoint hR\nhst : r.store = s'.store\nhhp : r.heap = s'.heap.union hR\n⊢ R r.store hR",
              "h": "<code>hst</code> replaces the big store by the small one, and then <code>(hc σ hP hp).2</code> — the universal half of the small triple — applies to <code>s'</code>."
            },
            {
              "tac": "· exact hpres ⟨σ, Heap.union hP hR⟩ r hex hR hr",
              "state": "No goals.",
              "h": "The frame assertion survives because the command preserves it. For <code>alloc x e</code> this is where you must know that <code>R</code> does not mention <code>x</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Reading the result honestly",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Put the three results side by side. <code>frameProperty_alloc</code>: proved. <code>Preserves</code>: available for any store-independent <code>R</code>, exactly as in M8. <code>SafetyMonotone</code>: disproved. Be careful about what that last one buys you, because the obvious inference is invalid: refuting a <i>sufficient</i> condition does not refute the conclusion, and “<code>hoare_frame</code>'s proof breaks” is not “the frame rule is false”."
            },
            {
              "t": "p",
              "h": "Here it happens to be false, and the same heap does it. Take the frame assertion to be “the heap is totally allocated”. The framed precondition is satisfiable — split it as <code>Heap.empty</code> for the small part and <code>fun _ => some 0</code> for the frame — and the framed triple then asserts <code>Safe</code> on a heap with no free cell:"
            },
            {
              "t": "code",
              "src": "def full : Assertion := fun _ h => h = fun _ => some 0\n\ntheorem alloc_frame_rule_false (x : Var) (v : Val) :\n    ¬ Hoare (aAnd (fact (fun σ => (Atom.const v).eval σ = v)) emp ∗ full)\n        (.alloc x (.const v))\n        ((aExists fun l => pure (fun σ => σ x = l) ∗ (l ↦ v)) ∗ full) := by\n  intro hfr\n  obtain ⟨⟨r, hex⟩, -⟩ :=\n    hfr (fun _ => 0) (Heap.union Heap.empty (fun _ => some 0))\n      ⟨Heap.empty, (fun _ => some 0), disjoint_empty_left _, rfl, ⟨rfl, rfl⟩, rfl⟩\n  cases hex with\n  | @alloc _ _ _ l hfresh =>\n      have hf : Heap.union Heap.empty (fun _ => some 0) l = none := hfresh\n      rw [union_empty_left] at hf\n      exact absurd hf (by simp)",
              "tag": "illustration",
              "cap": "Not “unprovable by this route” — false. The unframed premise is <code>hoare_alloc x (.const v) v</code> exactly, proved in exercise 2; <code>full</code> is store-independent, so <code>Preserves</code> holds; and <code>frameProperty_alloc</code> holds. Only <code>SafetyMonotone</code> is missing, and the conclusion is false."
            },
            {
              "t": "p",
              "h": "So the frame rule for <code>alloc</code> is not a theorem of this development — it is a theorem of the development you get after replacing <code>Heap</code> with a finite map, where no heap is totally allocated and the counterexample has nowhere to live."
            },
            {
              "t": "p",
              "h": "That is a more useful state of affairs than a chapter that quietly assumed finiteness from the start. The two properties have different characters: the frame property is about <i>what runs do</i> and is insensitive to the heap representation; safety monotonicity is about <i>which runs exist</i> and is entirely a fact about the shape of the heap type. Only one of them is a question about your programming language."
            }
          ]
        }
      ],
      "pitfall": "Trying to <code>rw</code> a heap lemma at something inversion produced. Everything inversion produces is phrased through <code>{ store := …, heap := … }.heap</code>, and <code>rw</code> matches <i>syntactically</i>: given <code>h0 : { store := …, heap := Heap.empty.write 0 v }.heap 0 = none</code>, the tactic <code>rw [write_same] at h0</code> fails with “Did not find an occurrence of the pattern <code>Heap.write ?h ?l ?v ?l</code>”, because the projection is still standing between the pattern and the term. Note the asymmetry, because it will confuse you otherwise: term-level application is fine. <code>union_eq_none.mp hfresh</code> succeeds on exactly the hypothesis <code>rw</code> refuses, since unification is allowed to unfold definitions and syntactic matching is not. The fix for the <code>rw</code> case is one line and you will need it repeatedly: <code>have hf' : Heap.union h hFrame l = none := hfresh</code>. Restating a hypothesis at the type you want is free when the types are definitionally equal.",
      "variants": "Drop <code>hd : Heap.disjoint h hFrame</code> from the frame property and the heap equation still holds — <code>write_union</code> needs no hypotheses — but the disjointness conjunct fails, and it fails away from the new cell, where the only thing that could have separated <code>h</code> from <code>hFrame</code> was <code>hd</code> itself. Reverse the direction back to small → big and you have <code>HeapLocal</code> again, which is refuted above. Weaken the conclusion of <code>HeapLocal</code> to allow the big run to end with a <i>different</i> store — tempting, since you would then re-choose the location — and <code>hoare_frame</code> breaks instead, at the step <code>rw [hst]</code>, because <code>Q</code> is then being asserted about a store that never occurred."
    },
    {
      "t": "ex",
      "id": "m14-4",
      "name": "alloc, initialise, free",
      "hard": false,
      "why": "Verify a program that allocates a cell, writes to it, reads it back and frees it, ending in <code>emp</code>. Four commands, and it is the first program in this course whose correctness proof has to consider a run you did not pick.",
      "setup": "Write <code>alloc x v ; [x] := w ; y := [x] ; free x</code> in the extended language and prove <code>Hoare emp … (pure (fun σ => σ y = w))</code>, demonic reading. You will need <code>x ≠ y</code>. Two obligations: exhibit one run (safety), and show every run lands in the postcondition. Prove it straight from the semantics rather than through a rule algebra — the existential in the alloc postcondition makes rule-based composition more painful than it is worth for four commands.",
      "hints": [
        "For safety you get to choose, so choose <code>l = 0</code>: in the empty heap it is free. Build the run with nested <code>Exec.seq</code> and let <code>refine</code> leave the three “address is allocated” side conditions as holes.",
        "Those three holes are enormous when printed and trivial in content. <code>simp [Atom.eval, Store.set, Heap.write]</code> closes the first two; the third needs <code>hne</code> as well, because the address of the <code>free</code> is read out of a store in which <code>y</code> has just been written.",
        "For correctness, <code>cases</code> three times through the nested <code>.seq</code>s and once per command — seven inversions, alternating. Use the <code>| @seq _ s1 _ _ _ ha hrest =></code> form so you can name the intermediate states, and <code>| @alloc _ _ _ l hfresh =></code> so you can name the allocator's choice.",
        "After the inversions the context is unusable. Extract the two facts you actually need — <code>Store.set σ x l x = l</code>, and the load's value — restate the load hypothesis at a readable type, then <code>clear</code> the four monsters.",
        "The final heap is <code>Heap.erase (Heap.write (Heap.write Heap.empty l v) l w) l</code>. Collapse it with <code>write_shadow</code>, then <code>write_empty</code>, then <code>erase_singleton</code>."
      ],
      "expl": "The program is trivial and the proof is not, for one reason: the postcondition has to hold for every location the allocator might have returned. That is the difference between verifying a program in a deterministic language and verifying one in a language with <code>malloc</code>, and it is visible in the proof as the split between “choose a run” and “invert a run”.",
      "walk": [
        {
          "tac": "intro σ h he ; subst he",
          "h": "Fix the state and use <code>emp</code> to replace the heap by <code>Heap.empty</code>."
        },
        {
          "tac": "constructor",
          "h": "Split the demonic triple into its two obligations. From here the proof is two unrelated arguments."
        },
        {
          "tac": "refine ⟨_, Exec.seq (Exec.alloc (l := 0) rfl) (Exec.seq (Exec.write (old := v) ?_) …)⟩",
          "h": "Safety: build one complete run, nesting <code>Exec.seq</code> to match the nesting of <code>.seq</code> in the program. <code>(old := v)</code> and <code>(v := w)</code> are supplied because those implicits are not determined by the goal — the goal is just <code>∃ s'</code>."
        },
        {
          "tac": "· simp [Atom.eval, Store.set, Heap.write]",
          "h": "Side condition for the write: the address <code>σ[x↦0] x = 0</code> is allocated, holding <code>v</code>. <code>simp</code> performs the store lookup and the heap lookup."
        },
        {
          "tac": "· simp [Atom.eval, Store.set, Heap.write]",
          "h": "Same, for the load."
        },
        {
          "tac": "· simp [Atom.eval, Store.set, Heap.write, hne]",
          "h": "Same, for the free — but now the store has <code>y</code> written into it, so reading <code>x</code> out of it needs <code>x ≠ y</code>. Remove <code>hne</code> and this is the goal that fails."
        },
        {
          "tac": "intro s' hex ; cases hex with | @seq _ s1 _ _ _ ha hrest =>",
          "h": "Correctness. Peel the first <code>.seq</code>, naming the state after the allocation."
        },
        {
          "tac": "cases ha with | @alloc _ _ _ l hfresh =>",
          "h": "Name the allocator's choice. From here on <code>l</code> is universally quantified — nothing may depend on it being <code>0</code>."
        },
        {
          "tac": "cases hrest with | @seq … => cases hw with | @write _ _ _ old hl =>",
          "h": "Peel and invert the write. <code>old</code> is the value that was there before; the proof never uses it, which is a small confirmation that the write rule really is agnostic about the old contents."
        },
        {
          "tac": "cases hrest2 with | @seq … => cases hld with | @load _ _ _ u hl2 =>",
          "h": "Peel and invert the load. <code>u</code> is the value the load actually saw. It is <i>not</i> definitionally <code>w</code>; you have to derive that."
        },
        {
          "tac": "cases hfr with | @free _ _ u2 hl3 =>",
          "h": "Invert the free. <code>u2</code> is never used — <code>free</code> does not care what was in the cell."
        },
        {
          "tac": "have hx1 : Store.set σ x l x = l := by simp [Store.set]",
          "h": "The address fact, isolated once so that it can be rewritten with repeatedly."
        },
        {
          "tac": "have hl2' : Heap.write (Heap.write Heap.empty l v) (Store.set σ x l x) w (Store.set σ x l x) = some u := hl2",
          "h": "Restate the load hypothesis at a readable type. This is the same proof term; only the display changes."
        },
        {
          "tac": "clear hl hl2 hl3 hfresh",
          "h": "The four hypotheses inversion produced are not needed any more, and they are enormous, because each is stated through the whole chain of state literals built up so far. Between them they run to about 170 printed lines: <code>hfresh</code> is one, the write's <code>hl</code> is twelve, the load's <code>hl2</code> is fifty, and the free's <code>hl3</code> is a hundred and four. Each is several times the size of the last, and that is not an accident — a command's premise is stated about the state the previous command produced, so the state literals nest one inside the next. <code>clear</code> makes the rest of the proof readable, and makes the goal state small enough to think about."
        },
        {
          "tac": "rw [hx1, write_same] at hl2'",
          "h": "Reduce the address to <code>l</code>, then look up the cell: <code>hl2' : some w = some u</code>."
        },
        {
          "tac": "have hu : w = u := by injection hl2'",
          "h": "<code>injection</code> is constructor injectivity: <code>some w = some u</code> yields <code>w = u</code>. This is the step that connects the value the program read to the value the specification promises."
        },
        {
          "tac": "have hx3 : Store.set (Store.set σ x l) y u x = l := by simp [Store.set, hne]",
          "h": "The address of the <code>free</code>, read out of the post-load store. <code>hne</code> is what stops <code>y</code>'s value from being returned."
        },
        {
          "tac": "refine ⟨?_, ?_⟩",
          "h": "<code>pure φ</code> is <code>fact φ ∧ emp</code>: a fact about the store and a claim that the heap is empty."
        },
        {
          "tac": "· show Store.set (Store.set σ x l) y u y = w ; simp [Store.set, hu]",
          "h": "The variable <code>y</code> holds <code>u</code>, and <code>hu</code> says that is <code>w</code>."
        },
        {
          "tac": "· show Heap.erase (Heap.write (Heap.write Heap.empty l v) (Store.set σ x l x) w) (…) = Heap.empty",
          "h": "The heap obligation, restated readably."
        },
        {
          "tac": "  rw [hx1, hx3, write_shadow, write_empty, erase_singleton]",
          "h": "Five rewrites in a row, each named after exactly what it does: fix both addresses to <code>l</code>, collapse the double write, turn the write on the empty heap into a singleton, erase the singleton. The heap is empty again — no leak."
        }
      ],
      "deep": [
        {
          "t": "code",
          "src": "def allocInitFree (x y : Var) (v w : Val) : Cmd :=\n  .seq (.alloc x (.const v))\n    (.seq (.write (.var x) (.const w))\n      (.seq (.load y (.var x)) (.free (.var x))))",
          "tag": "illustration"
        },
        {
          "t": "code",
          "src": "theorem allocInitFree_spec (x y : Var) (v w : Val) (hne : x ≠ y) :\n    Hoare emp (allocInitFree x y v w) (pure (fun σ => σ y = w)) := by\n  intro σ h he\n  subst he\n  constructor\n  · refine ⟨_, Exec.seq (Exec.alloc (l := 0) rfl)\n              (Exec.seq (Exec.write (old := v) ?_)\n                (Exec.seq (Exec.load (v := w) ?_) (Exec.free (v := w) ?_)))⟩\n    · simp [Atom.eval, Store.set, Heap.write]\n    · simp [Atom.eval, Store.set, Heap.write]\n    · simp [Atom.eval, Store.set, Heap.write, hne]\n  · intro s' hex\n    cases hex with\n    | @seq _ s1 _ _ _ ha hrest =>\n      cases ha with\n      | @alloc _ _ _ l hfresh =>\n        cases hrest with\n        | @seq _ s2 _ _ _ hw hrest2 =>\n          cases hw with\n          | @write _ _ _ old hl =>\n            cases hrest2 with\n            | @seq _ s3 _ _ _ hld hfr =>\n              cases hld with\n              | @load _ _ _ u hl2 =>\n                cases hfr with\n                | @free _ _ u2 hl3 =>\n                  have hx1 : Store.set σ x l x = l := by simp [Store.set]\n                  have hl2' : Heap.write (Heap.write Heap.empty l v)\n                                (Store.set σ x l x) w (Store.set σ x l x) = some u := hl2\n                  clear hl hl2 hl3 hfresh\n                  rw [hx1, write_same] at hl2'\n                  have hu : w = u := by injection hl2'\n                  have hx3 : Store.set (Store.set σ x l) y u x = l := by\n                    simp [Store.set, hne]\n                  refine ⟨?_, ?_⟩\n                  · show Store.set (Store.set σ x l) y u y = w\n                    simp [Store.set, hu]\n                  · show Heap.erase (Heap.write (Heap.write Heap.empty l v)\n                            (Store.set σ x l x) w)\n                          (Store.set (Store.set σ x l) y u x) = Heap.empty\n                    rw [hx1, hx3, write_shadow, write_empty, erase_singleton]",
          "tag": "illustration"
        },
        {
          "t": "trace",
          "title": "allocInitFree_spec — the two obligations",
          "start": "x y : Var\nv w : Val\nhne : x ≠ y\n⊢ Hoare emp (allocInitFree x y v w) (_root_.pure fun σ => σ y = w)",
          "steps": [
            {
              "tac": "intro σ h he",
              "state": "x y : Var\nv w : Val\nhne : x ≠ y\nσ : Store\nh : Heap\nhe : emp σ h\n⊢ Safe (allocInitFree x y v w) { store := σ, heap := h } ∧\n    ∀ (s' : State),\n      Exec (allocInitFree x y v w) { store := σ, heap := h } s' → _root_.pure (fun σ => σ y = w) s'.store s'.heap",
              "h": "The two halves. Everything after this is one or the other."
            },
            {
              "tac": "subst he ; constructor",
              "state": "case left\nx y : Var\nv w : Val\nhne : x ≠ y\nσ : Store\n⊢ Safe (allocInitFree x y v w) { store := σ, heap := Heap.empty }",
              "h": "The safety goal. This is the one where you are allowed to choose the allocator's answer."
            },
            {
              "tac": "refine ⟨_, Exec.seq (Exec.alloc (l := 0) rfl) …⟩",
              "state": "case left.refine_1\nx y : Var\nv w : Val\nhne : x ≠ y\nσ : Store\n⊢ { store := { store := σ, heap := Heap.empty }.store.set x 0,\n          heap :=\n            { store := σ, heap := Heap.empty }.heap.write 0\n              (Atom.eval { store := σ, heap := Heap.empty }.store (Atom.const v)) }.heap\n      (Atom.eval\n        { store := { store := σ, heap := Heap.empty }.store.set x 0,\n            heap :=\n              { store := σ, heap := Heap.empty }.heap.write 0\n                (Atom.eval { store := σ, heap := Heap.empty }.store (Atom.const v)) }.store\n        (Atom.var x)) =\n    some v",
              "h": "The first side condition, printed in full so that you know what you are in for. It says: after allocating cell <code>0</code> holding <code>v</code>, the address <code>x</code> denotes an allocated cell holding <code>v</code>. It is eleven lines; the second is forty-nine and the third is a hundred and three. Nothing in any of them is hard — it is all projection noise, and <code>simp</code> eats it. Unfolding <code>Atom.eval</code> turns <code>Atom.var x</code> into a store lookup, unfolding <code>Store.set</code> turns that into an <code>if x = x</code> which the <code>↓reduceIte</code> simproc evaluates, and unfolding <code>Heap.write</code> turns the heap lookup into an <code>if 0 = 0</code> which goes the same way."
            },
            {
              "tac": "· simp [Atom.eval, Store.set, Heap.write] (×3, last with hne)",
              "state": "case right\nx y : Var\nv w : Val\nhne : x ≠ y\nσ : Store\n⊢ ∀ (s' : State),\n    Exec (allocInitFree x y v w) { store := σ, heap := Heap.empty } s' → _root_.pure (fun σ => σ y = w) s'.store s'.heap",
              "h": "Safety done. Now the half that has to hold for every run."
            },
            {
              "tac": "cases × 7, then have hx1 / have hl2' / clear hl hl2 hl3 hfresh",
              "state": "case right.seq.alloc.seq.write.seq.load.free\nx y : Var\nv w : Val\nhne : x ≠ y\nσ : Store\nl old u u2 : Val\nhx1 : σ.set x l x = l\nhl2' : (Heap.empty.write l v).write (σ.set x l x) w (σ.set x l x) = some u\n⊢ _root_.pure (fun σ => σ y = w) …",
              "h": "This is the context <i>after</i> <code>clear</code>; before it, four hypotheses running to about 170 lines between them. The case name records the whole inversion path. Three unknowns survive: <code>l</code> (what the allocator chose), <code>u</code> (what the load saw), and <code>old</code>/<code>u2</code> (what was in the cell before the write and the free — never used). The goal is still displayed through the full chain of state literals; that is what the two <code>show</code>s below are for."
            },
            {
              "tac": "refine ⟨?_, ?_⟩ ; show Store.set (Store.set σ x l) y u y = w",
              "state": "case right.seq.alloc.seq.write.seq.load.free.refine_1\nx y : Var\nv w : Val\nhne : x ≠ y\nσ : Store\nl old u u2 : Val\nhx1 : σ.set x l x = l\nhl2' : some w = some u\nhu : w = u\nhx3 : (σ.set x l).set y u x = l\n⊢ (σ.set x l).set y u y = w",
              "h": "Readable at last, and true by <code>hu</code>."
            },
            {
              "tac": "· simp [Store.set, hu] ; · show Heap.erase … = Heap.empty",
              "state": "case right.seq.alloc.seq.write.seq.load.free.refine_2\nx y : Var\nv w : Val\nhne : x ≠ y\nσ : Store\nl old u u2 : Val\nhx1 : σ.set x l x = l\nhl2' : some w = some u\nhu : w = u\nhx3 : (σ.set x l).set y u x = l\n⊢ ((Heap.empty.write l v).write (σ.set x l x) w).erase ((σ.set x l).set y u x) = Heap.empty",
              "h": "The whole heap history in one term: empty, write <code>v</code>, write <code>w</code>, erase. Both addresses reduce to <code>l</code> — <code>hx1</code> and <code>hx3</code> — and then three heap lemmas finish it."
            },
            {
              "tac": "rw [hx1, hx3, write_shadow, write_empty, erase_singleton]",
              "state": "No goals.",
              "h": ""
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The heap, four commands long",
          "items": [
            {
              "k": "after alloc",
              "h": "<code>Heap.write Heap.empty l v</code> — one cell, at a location you did not choose and cannot name."
            },
            {
              "k": "after the write",
              "h": "<code>Heap.write (Heap.write Heap.empty l v) l w</code>. Two writes to the same location; <code>write_shadow</code> collapses them."
            },
            {
              "k": "after the load",
              "h": "unchanged — <code>load</code> touches only the store."
            },
            {
              "k": "after the free",
              "h": "<code>Heap.erase (Heap.write Heap.empty l w) l</code>, which is <code>Heap.erase (Heap.singleton l w) l</code>, which is <code>Heap.empty</code>. The postcondition <code>emp</code> is the no-leak claim, and it is a claim about a location the specification never names."
            }
          ]
        },
        {
          "t": "detail",
          "title": "Why not build this out of the rules",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "M9 verified <code>copyCell</code> and <code>moveCell</code> through <code>hoare_seq</code>, <code>hoare_frame</code> and <code>hoare_consequence</code>, and that is the right way to scale. Here it is more work, for a specific reason: the postcondition of <code>hoare_alloc</code> is <code>aExists</code>, so the intermediate assertion you would feed to <code>hoare_seq</code> has to carry the existential through three more commands, and each of the small-footprint rules would first have to be lifted over it."
            },
            {
              "t": "p",
              "h": "The standard fix is an existential-elimination rule for triples — <code>(∀ a, Hoare (P a) c Q) → Hoare (aExists P) c Q</code> — which is three lines under the demonic definition and turns the rule-based route back into the shorter one. Proving it and redoing this exercise through the rules is a good fifth exercise if you want one."
            }
          ]
        }
      ],
      "pitfall": "Forgetting <code>x ≠ y</code>. The program reads the cell into <code>y</code> and then frees the cell whose address is in <code>x</code>; if <code>x</code> and <code>y</code> are the same variable, the <code>free</code> addresses <code>w</code>, not <code>l</code>, and the program is not even safe. The failure shows up as an unsolved <code>simp</code> goal of the form <code>x = y → ¬w = 0 → (if x = y → w = 0 then some v else Heap.empty (if x = y then w else 0)) = some w</code> — which is <code>simp</code> telling you, in its own way, that you have an aliasing bug.",
      "variants": "Drop the <code>free</code> and the postcondition becomes <code>∃ l, pure (σ y = w) ∗ l ↦ w</code>: still true, but no longer <code>emp</code>, and the leaked cell is now part of the caller's obligation forever. Swap the load and the free and the program is unsafe — the second obligation would still be provable, vacuously, because no run exists, which is a good illustration of why the <code>Safe</code> conjunct has to be there. Replace the initial value <code>.const v</code> by <code>.var x</code> and the specification stops meaning what you think: <code>alloc</code> evaluates its argument in the store <i>before</i> writing <code>x</code>, so the cell holds the old <code>σ x</code>, not the new location."
    },
    {
      "t": "h3",
      "s": "Where this leaves the development"
    },
    {
      "t": "p",
      "h": "Allocation is the only construct in this course that forces you to change a <i>definition</i> rather than add a rule. Everything else — the wand, weakest preconditions, loops — was built on top of M6's triple without touching it. Here the triple itself is wrong, the locality condition is wrong, and the heap type is wrong, and each of those is discovered by trying to prove something and failing in a specific place."
    },
    {
      "t": "p",
      "h": "That is a good note to leave the development on, because it is the honest summary of what a semantic proof gives you: not a guarantee that your definitions are right, but a reliable way of finding out where they are not."
    },
    {
      "t": "dod",
      "h": "You can add allocation to the language, say why the small-footprint rule must quantify existentially over the returned location, distinguish the angelic and demonic readings of a triple and explain why nondeterminism forces the second, exhibit the heap on which <code>HeapLocal</code> fails for <code>alloc</code>, and name which half of locality survives functional heaps and which half needs finite ones."
    }
  ]
});
