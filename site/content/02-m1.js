/* M1 — Heaps as partial functions
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m1",
  "num": "M1",
  "phase": "Phase 1 · Semantic foundations",
  "title": "Heaps as partial functions",
  "blurb": "The four primitive heap operations, and the lookup equations that characterise them.",

  "orient": {
    "youWill": [
      "Read <code>Heap := Loc → Option Val</code> as a partial function, and say exactly what <code>Heap.singleton l v</code> owns and what it does not.",
      "Prove a <i>pointwise</i> lookup equation with a single <code>simp [Heap.write, hne]</code> — and say what <code>simp</code> actually did to get there.",
      "Prove an equation between two <i>heaps</i> with the <code>funext</code> → <code>by_cases</code> → <code>simp</code> pattern, which is the shape of every heap identity in the next three chapters.",
      "Drive a nested-<code>if</code> goal by hand with <code>rw [if_pos …]</code> / <code>rw [if_neg …]</code> when you want to watch each branch collapse.",
      "Point at the single line of <code>write_comm</code> where non-aliasing is used, and produce the counterexample that appears the moment you delete it."
    ],
    "needs": [
      "M0, and only M0: <code>funext</code>, <code>by_cases</code>, <code>simp [f]</code>, <code>if_pos</code> / <code>if_neg</code>, and the four <code>update</code> lemmas. M1 is those same four proofs run again with <code>Option Val</code> in the codomain instead of <code>Nat</code>.",
      "No imports, no Mathlib. Everything you may use is in the chapter, and there is nothing else in scope."
    ],
    "payoff": "Every heap manipulation for the rest of the course — the write rule, the free rule, the frame rule, symbolic execution — is a rewrite with one of the equations you prove here. After this chapter you should never unfold a heap operation again."
  },

  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "p",
      "h": "A heap is a partial function <code>Loc ⇀ Val</code>. We encode partiality with <code>Option</code>, so a heap is a total function <code>Loc → Option Val</code> and “undefined” is the value <code>none</code>."
    },
    {
      "t": "cmp",
      "left": {
        "t": "What you would write on paper",
        "kind": "good",
        "h": "“Let <code>h : Loc ⇀ Val</code> be a partial function.” The domain <code>dom h</code> is part of the data, <code>h(l)</code> is a <i>value</i>, and it is simply meaningless to write <code>h(l)</code> for <code>l ∉ dom h</code>."
      },
      "right": {
        "t": "What Lean gets",
        "h": "A total function into <code>Option Val</code>. Every location has an answer; the answer at an unallocated location is <code>none</code>. The domain is not stored anywhere — it is recovered, when you need it, as <code>{l | h l ≠ none}</code>.",
        "src": "abbrev Loc   := Nat\nabbrev Val   := Nat\nabbrev Heap  := Loc → Option Val"
      }
    },
    {
      "t": "p",
      "h": "That translation is the first real design decision in the course, so it is worth saying what it bought and what it cost. It bought <b>pointwise everything</b>: heap equality is function equality, so <code>funext</code> applies; heap update is function update, so there is nothing to unfold beyond an <code>if</code>; and no operation ever has to carry a side condition about domains in its <i>type</i>. It cost you the ability to write <code>h(l)</code> and get a <code>Val</code>: every lookup returns an <code>Option</code>, and every proof about a lookup eventually splits on <code>none</code> versus <code>some v</code>."
    },
    {
      "t": "detail",
      "title": "What <code>Option</code> is, and the two facts about it you actually use",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "<code>Option</code> is an ordinary inductive type with two constructors and no magic. <code>#print Option</code> says so:"
        },
        {
          "t": "state",
          "src": "inductive Option.{u} : Type u → Type u\nnumber of parameters: 1\nconstructors:\nOption.none : {α : Type u} → Option α\nOption.some : {α : Type u} → α → Option α"
        },
        {
          "t": "p",
          "h": "Two consequences carry every proof in this chapter, and both come for free from <code>none</code> and <code>some</code> being <i>distinct constructors</i> of an inductive type. First, <code>some v</code> is never <code>none</code>. Second, <code>some</code> is injective, so an equation between two defined cells is an equation between their values — wrapping in <code>some</code> loses nothing."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "example (v : Val) : some v ≠ none := by simp\n\nexample (v w : Val) (heq : (some v : Option Val) = some w) : v = w :=\n  Option.some.inj heq"
        },
        {
          "t": "p",
          "h": "The first fact is doing more work than it looks. Run <code>simp?</code> on <code>singleton_other</code> with the hypothesis withheld and Lean prints the whole mechanism:"
        },
        {
          "t": "state",
          "src": "Try this:\n  [apply] simp only [Heap.singleton, ite_eq_right_iff, reduceCtorEq, imp_false]",
          "cap": "simp? on `simp [Heap.singleton]` for the goal Heap.singleton l v x = none."
        },
        {
          "t": "p",
          "h": "Read it right to left. <code>ite_eq_right_iff</code> turns <code>(if c then a else b) = b</code> into <code>c → a = b</code>; here that is <code>x = l → some v = none</code>. <code>reduceCtorEq</code> then observes that <code>some</code> and <code>none</code> are different constructors and replaces <code>some v = none</code> by <code>False</code>. <code>imp_false</code> rewrites <code>x = l → False</code> to <code>¬x = l</code>. Those three names explain almost every residue you will see in this chapter, and they are the reason <code>simp</code>'s failures here are informative rather than opaque."
        }
      ]
    },
    {
      "t": "detail",
      "title": "Three encodings of partiality that were rejected, and what each one breaks",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "dl",
          "items": [
            {
              "k": "A dependent pair <code>(D : Loc → Prop, f : ∀ l, D l → Val)</code>",
              "h": "The mathematically honest encoding: carry the domain and a function defined on it. It dies immediately on <i>equality</i>. Two heaps are equal when their domains are equal <i>and</i> their functions agree modulo the transported domain proof. That is a heap-equality lemma with a <code>cast</code> in it, and every single proof in M1 and M2 would have to reason about proof-irrelevant transport. <code>funext</code> would no longer be the tool."
            },
            {
              "k": "<code>Loc → Val</code> with a sentinel value for “unallocated”",
              "h": "Total, simple, and wrong. There is then no heap with empty domain distinguishable from the heap that stores the sentinel everywhere, so <code>emp</code> collapses, and <code>Heap.disjoint</code> in M2 cannot be stated. Separation logic is entirely about who owns which cells; an encoding that cannot say “this cell is not mine” has nothing to work with."
            },
            {
              "k": "A finite map — association list, red–black tree, <code>Std.HashMap</code>",
              "h": "Executable and decidable, which sounds attractive. The price is that heap extensionality is no longer <code>funext</code> but a lemma about the representation modulo permutation and duplicate keys, and <code>Heap.union</code> in M2 needs a canonical-form argument before it is even well defined. We want the <i>algebra</i> of heaps, not a data structure. M14 revisits this: with finite heaps you can prove a fresh location exists, which is exactly what allocation needs and what our encoding cannot give you."
            }
          ]
        },
        {
          "t": "p",
          "h": "Note the consequence of the choice we made: nothing in <code>Loc → Option Val</code> forces the domain to be finite. Our heaps may be infinite. Nothing in M1–M13 needs finiteness, which is why the omission is free; M14 is where it has to be confronted."
        }
      ]
    },
    {
      "t": "p",
      "h": "The word to unlearn here is <b>mutation</b>. Inside Lean nothing mutates. <code>Heap.write h l v</code> is not an instruction; it is a <i>new function</i>, defined pointwise from <code>h</code>. When the operational semantics says “the command writes to memory”, what it really says is “the state after is the one whose heap is <code>Heap.write h l v</code>”."
    },
    {
      "t": "p",
      "h": "Take that literally, because it is what makes this chapter possible at all. There is no “<code>h</code> before” and “<code>h</code> after”: there are two heaps, <code>h</code> and <code>Heap.write h l v</code>, and both exist at once, in the same context, available to be compared. A statement like <code>write_shadow</code> — <i>writing twice to <code>l</code> is the same heap as writing once</i> — is not even expressible in a language with real mutation, because by the time the second write has happened the first heap is gone. Here it is an equation between two values, and you prove it by evaluating both at an arbitrary location."
    },
    {
      "t": "code",
      "src": "def empty : Heap := fun _ => none\n\ndef singleton (l : Loc) (v : Val) : Heap :=\n  fun x => if x = l then some v else none\n\ndef write (h : Heap) (l : Loc) (v : Val) : Heap :=\n  fun x => if x = l then some v else h x\n\ndef erase (h : Heap) (l : Loc) : Heap :=\n  fun x => if x = l then none else h x\n\nend Heap"
    },
    {
      "t": "anat",
      "src": "namespace Heap\n\ndef empty : Heap := fun _ => none\n\ndef singleton (l : Loc) (v : Val) : Heap :=\n  fun x => if x = l then some v else none\n\ndef write (h : Heap) (l : Loc) (v : Val) : Heap :=\n  fun x => if x = l then some v else h x\n\ndef erase (h : Heap) (l : Loc) : Heap :=\n  fun x => if x = l then none else h x\n\nend Heap",
      "cap": "The same four definitions with the namespace line the excerpt above leaves implicit.",
      "parts": [
        {
          "m": "namespace Heap",
          "h": "This is where the dangling <code>end Heap</code> in the excerpt comes from. Inside the block the definitions are written <code>empty</code>, <code>singleton</code>, <code>write</code>, <code>erase</code>; from outside — which is everywhere else in the course — they are <code>Heap.empty</code>, <code>Heap.singleton</code>, <code>Heap.write</code>, <code>Heap.erase</code>. Names like <code>write</code> and <code>erase</code> are far too generic to sit at top level."
        },
        {
          "m": "fun _ => none",
          "h": "The empty heap: undefined at every location. The argument is written <code>_</code> rather than <code>x</code> because it is never mentioned; name it and Lean's linter objects with <code>Variable name `x` is not explicitly referenced</code>. Nothing breaks, but the underscore is the intended spelling for “I do not care what this is”."
        },
        {
          "m": "if x = l then some v else none",
          "h": "The singleton. Read the two branches as the two halves of the specification: at <code>l</code> the value is <code>v</code>; <i>everywhere else it is undefined</i>. The second half is the one you will keep having to defend, and it is exactly <code>singleton_other</code> below."
        },
        {
          "m": "else h x",
          "h": "This is what makes <code>write</code> an <i>override</i> rather than a fresh heap: off <code>l</code> it defers to <code>h</code>. Note the direction of the test — <code>x = l</code>, the bound variable on the left. That order is not cosmetic: your disequality hypotheses have to be stated as <code>x ≠ l</code> to match it, or <code>simp</code> will not fire."
        },
        {
          "m": "if x = l then none else h x",
          "h": "<code>erase</code> is <code>write</code> with <code>none</code> in the then-branch. Every proof about <code>erase</code> in this chapter is the corresponding proof about <code>write</code> with one token changed, which is why the exercises come in pairs."
        }
      ]
    },
    {
      "t": "note",
      "kind": "info",
      "title": "Lean will not show you the name you typed",
      "h": "Because <code>h : Heap</code> and the definitions live in the <code>Heap</code> namespace, Lean's pretty-printer renders <code>Heap.write h l v</code> as <code>h.write l v</code>. This is generalised field notation, and it is applied on output whether or not you used it on input. So a goal you typed as <code>Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂</code> comes back looking like this:"
    },
    {
      "t": "state",
      "src": "h : Heap\nl : Loc\nv₁ v₂ : Val\n⊢ (h.write l v₁).write l v₂ = h.write l v₂",
      "cap": "The goal of write_shadow, as Lean actually prints it."
    },
    {
      "t": "p",
      "h": "Those are the same term. You may type either form — <code>h.write l v</code> elaborates fine — but the goal displays will always use the dotted one, so learn to read it now. Every <code>trace</code> block in this chapter is copied from Lean's output, dots and all."
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>Heap.empty</code>",
          "h": "Domain <code>∅</code>. This is the unit of the resource monoid in M2 and the assertion <code>emp</code> in M3."
        },
        {
          "k": "<code>Heap.singleton l v</code>",
          "h": "Domain exactly <code>{l}</code>. This is the assertion <code>l ↦ v</code>, and the word <i>exactly</i> is doing all the work — see the callout below."
        },
        {
          "k": "<code>Heap.write h l v</code>",
          "h": "Domain <code>dom h ∪ {l}</code>. Read that again: <b>write allocates</b> if <code>l</code> was not already there. Nothing in the definition prevents it. The separation-logic write rule will restore the intended meaning by demanding <code>l ↦ _</code> in its precondition, which is what guarantees <code>l ∈ dom h</code> before the write."
        },
        {
          "k": "<code>Heap.erase h l</code>",
          "h": "Domain <code>dom h \\ {l}</code>. Symmetrically, erase is happy to erase a location that was never there; it is the identity in that case."
        }
      ]
    },
    {
      "t": "note",
      "h": "<code>Heap.singleton l v</code> is the heap whose <b>entire domain</b> is <code>{l}</code>. It is not “a heap containing <code>l ↦ v</code> somewhere among other cells”. This exactness is the whole design, and if you slip on it once, the free rule becomes unsound. Hold on to it.",
      "title": "The one thing to remember",
      "kind": "key"
    },
    {
      "t": "p",
      "h": "Compare the two readings of “<code>l</code> points to <code>v</code>”:"
    },
    {
      "t": "txt",
      "src": "  exact  (ours):    h = Heap.singleton l v      -- dom h = {l}\n  inexact (wrong):  h l = some v                 -- l ∈ dom h, and who knows what else"
    },
    {
      "t": "p",
      "h": "The inexact reading is the one you would write first, and it is the one that makes <code>{l ↦ v} free l {emp}</code> false: freeing one cell of a big heap does not leave the heap empty. With the exact reading, the rule is correct as stated, and big heaps are handled later by the frame rule. That is the trade separation logic makes: <b>tiny, exact specifications plus one structural rule</b>, instead of big specifications with side conditions."
    },
    {
      "t": "p",
      "h": "The gap between the two readings is not rhetorical; it is a pair of theorems. Here is the two-cell heap <code>{0 ↦ 5, 1 ↦ 6}</code>, which satisfies the inexact reading of “<code>0</code> points to <code>5</code>” and refutes the exact one:"
    },
    {
      "t": "code",
      "tag": "illustration",
      "cap": "The inexact reading holds; the exact reading fails. The witness is the location 1, which the singleton does not own.",
      "src": "-- the two-cell heap {0 ↦ 5, 1 ↦ 6} does satisfy the inexact reading …\nexample : Heap.write (Heap.singleton 0 5) 1 6 0 = some 5 := by\n  rw [write_other _ _ _ _ (by simp), singleton_same]\n\n-- … and is not the singleton heap at 0.\nexample : Heap.write (Heap.singleton 0 5) 1 6 ≠ Heap.singleton 0 5 := by\n  intro heq\n  have h1 := congrFun heq 1\n  rw [write_same, singleton_other 0 1 5 (by simp)] at h1\n  exact absurd h1 (by simp)"
    },
    {
      "t": "p",
      "h": "<code>congrFun heq 1</code> is worth naming, because it is the converse of <code>funext</code> and you will want it whenever you need to <i>refute</i> a heap equation: from <code>heq : f = g</code> it produces <code>f 1 = g 1</code>. To prove two heaps equal you go pointwise with <code>funext</code>; to prove them different you exhibit one point with <code>congrFun</code>."
    },
    {
      "t": "p",
      "h": "Two pieces of syntax in that snippet, since this is the first place they appear. <code>write_other _ _ _ _ (by simp)</code> supplies <code>write_other</code>'s five explicit arguments — <code>h</code>, <code>l</code>, <code>x</code>, <code>v</code>, and the disequality — with an <code>_</code> wherever unification can read the value off the goal, which is all four of the first ones; only the proof has to be given, and <code>by simp</code> gives it inline, because <code>0 ≠ 1</code> is a fact about numerals rather than variables. The lemmas being applied — <code>write_other</code>, <code>write_same</code>, <code>singleton_same</code>, <code>singleton_other</code> — are the ones you are about to prove. Nothing here depends on them; the snippet is placed early because the point it makes is about the definitions, not about the proofs."
    },
    {
      "t": "detail",
      "title": "Why Loc, Val and Heap are abbrev and not def",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "<code>abbrev</code> is <code>def</code> plus <code>@[reducible]</code>. The reducibility is not decoration. Type-class synthesis unfolds reducible definitions and stops at irreducible ones, so with <code>abbrev Loc := Nat</code> Lean can find the <code>Decidable (x = l)</code> instance that <code>if x = l then … else …</code> requires — it is <code>Nat.decEq</code>. Make <code>Loc</code> a plain <code>def</code> and the same four definitions no longer typecheck:"
        },
        {
          "t": "code",
          "tag": "sketch",
          "cap": "This does not compile — that is the point.",
          "src": "def MyLoc := Nat\ndef MyVal := Nat\ndef MyHeap := MyLoc → Option MyVal\n\ndef ms (l : MyLoc) (v : MyVal) : MyHeap :=\n  fun x => if x = l then some v else none"
        },
        {
          "t": "state",
          "src": "error(lean.synthInstanceFailed): failed to synthesize instance of type class\n  Decidable (x = l)",
          "cap": "Lean's complaint, without its file position: it cannot see that MyLoc is Nat, so it cannot find Nat.decEq."
        },
        {
          "t": "p",
          "h": "So <code>abbrev</code> here is what buys you decidable equality on locations for free. It also means <code>Loc</code> and <code>Val</code> are <i>literally the same type</i>, which is a genuine wart: nothing stops you passing a value where a location is expected. In a production development you would use single-field structures and pay for the wrappers. For a workbook the noise is not worth it — but if a proof ever goes strange, check that you have not swapped a location for a value."
        }
      ]
    },
    {
      "t": "sec",
      "s": "Exercises · lookup equations"
    },
    {
      "t": "p",
      "h": "These six lemmas are the interface. Once they are proved you should never unfold <code>Heap.write</code> again."
    },
    {
      "t": "steps",
      "title": "The only two proof shapes in this chapter",
      "items": [
        {
          "k": "A pointwise equation",
          "h": [
            {
              "t": "p",
              "h": "The goal has the form <code>… x = …</code> and is an equation in <code>Option Val</code>. There is a definition to unfold and then an <code>if</code> to collapse, and collapsing it needs to know whether the condition holds. If the statement tells you (<code>x</code> is literally <code>l</code>, or you were handed <code>hne : x ≠ l</code>) it is one <code>simp</code>. Exercises 1 through 4 are all of this shape."
            }
          ]
        },
        {
          "k": "An equation between heaps",
          "h": [
            {
              "t": "p",
              "h": "The goal has the form <code>h₁ = h₂</code> where both sides are heaps, i.e. <i>functions</i>. Nothing can happen until you go pointwise, because <code>simp</code> will not even unfold <code>Heap.write</code> in an unapplied position. So:"
            },
            {
              "t": "code",
              "tag": "sketch",
              "src": "funext x\nby_cases hx : x = l <;> simp [Heap.write, hx]"
            },
            {
              "t": "p",
              "h": "<code>funext x</code> turns the function equation into an equation at an arbitrary <code>x</code>, which puts you back in shape 1 — except that now nobody has told you how <code>x</code> relates to <code>l</code>, so you supply the missing information yourself with <code>by_cases</code>. Exercises 5 through 8 are all of this shape."
            }
          ]
        }
      ]
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>simp [Heap.write]</code>",
          "h": "Adds the defining equation of <code>Heap.write</code> to the rewrite set, left to right. It fires only on an <i>applied</i> occurrence <code>Heap.write h l v x</code>. On the unapplied <code>Heap.write h l v</code> it does nothing at all — Lean answers <code>`simp` made no progress</code> — and that is precisely why <code>funext</code> has to come first."
        },
        {
          "k": "<code>simp [hne]</code> for <code>hne : x ≠ l</code>",
          "h": "A hypothesis that is a negation is added as the rewrite <code>(x = l) ↦ False</code>. Once the condition of the <code>if</code> is the literal <code>False</code>, the <code>if</code> can go."
        },
        {
          "k": "<code>simp [hx]</code> for <code>hx : x = l</code>",
          "h": "A hypothesis that is an equation is added as the rewrite <code>x ↦ l</code>, after which every <code>x = l</code> in the goal becomes <code>l = l</code> and then <code>True</code>."
        },
        {
          "k": "<code>↓reduceIte</code>",
          "h": "The simp procedure that actually deletes an <code>if</code> whose condition has become <code>True</code> or <code>False</code>. You never write it; you see it if you run <code>simp?</code> instead of <code>simp</code>, which prints the exact <code>simp only [...]</code> call that closed your goal. Running <code>simp?</code> once on each of these exercises is the cheapest way to stop treating <code>simp</code> as magic."
        }
      ]
    },
    {
      "t": "ex",
      "id": "m1-1",
      "name": "singleton_same",
      "hard": false,
      "why": "The first of the equations that make up the heap interface. Mathematically it is nothing; the point is to watch an <code>if</code> disappear, and to notice that the right-hand side is <code>some v</code> and not <code>v</code>. Every read from a heap returns an <code>Option</code>, and that <code>some</code> is what forces the case analysis in every lookup proof from M5 onwards.",
      "setup": "In scope: the four definitions above, and nothing else. <code>singleton</code> was defined inside <code>namespace Heap</code>, so from here you must call it <code>Heap.singleton</code> — including inside the <code>simp</code> set.",
      "goal": "theorem singleton_same (l : Loc) (v : Val) :\n    Heap.singleton l v l = some v",
      "hints": [
        "Nothing in this goal is primitive. <code>Heap.singleton</code> is a definition, and until it is unfolded there is no <code>if</code> for any tactic to act on. Which tactic takes a definition <i>name</i> as an argument?",
        "<code>simp [Heap.singleton]</code>. Passing a name to <code>simp</code> adds that definition's equation to the rewrite set.",
        "<code>simp [Heap.singleton]</code> is the entire proof. After the unfolding the goal is <code>(if l = l then some v else none) = some v</code>, and <code>simp</code> discharges <code>if l = l</code> without further help."
      ],
      "sol": "theorem singleton_same (l : Loc) (v : Val) :\n    Heap.singleton l v l = some v := by\n  simp [Heap.singleton]",
      "expl": "Unfold and discharge <code>if l = l</code>. Nothing else happens.",
      "walk": [
        {
          "tac": "simp [Heap.singleton]",
          "h": "Rewrites <code>Heap.singleton l v l</code> to <code>if l = l then some v else none</code>, notices that the condition <code>l = l</code> is <code>True</code>, deletes the <code>if</code>, and closes the resulting <code>some v = some v</code> by reflexivity."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "singleton_same, with the unfolding made visible",
          "start": "l : Loc\nv : Val\n⊢ Heap.singleton l v l = some v",
          "steps": [
            {
              "tac": "unfold Heap.singleton",
              "state": "l : Loc\nv : Val\n⊢ (if l = l then some v else none) = some v",
              "h": "This is the step <code>simp [Heap.singleton]</code> performs silently. <code>unfold</code> is worth reaching for exactly once per definition, to see what you are working with."
            },
            {
              "tac": "simp",
              "state": "No goals.",
              "h": "The condition is <code>l = l</code>; <code>simp</code> proves it by <code>rfl</code>, replaces it by <code>True</code>, and <code>↓reduceIte</code> removes the <code>if</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "What simp actually used",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Replace <code>simp</code> by <code>simp?</code> and Lean prints the minimal call it found:"
            },
            {
              "t": "state",
              "src": "Try this:\n  [apply] simp only [Heap.singleton, ↓reduceIte]"
            },
            {
              "t": "p",
              "h": "Two rewrites: the definition, and the simp procedure that eliminates a decided <code>if</code>. No search, no arithmetic, no hidden lemma library. Every <code>simp</code> in this chapter is this small, and <code>simp?</code> will show you so."
            }
          ]
        }
      ],
      "pitfall": "Bare <code>simp</code> fails here with <code>`simp` made no progress</code>: <code>simp</code> does not unfold definitions you have not named. <code>rfl</code> fails too, which surprises people — the statement looks like it should hold by computation. It does not, because <code>if l = l</code> can only compute once <code>Nat.decEq l l</code> computes, and <code>l</code> is a variable, so it is stuck. Lean says so in as many words: <code>Tactic `rfl` failed: The left-hand side Heap.singleton l v l is not definitionally equal to the right-hand side some v</code>, and then reprints the goal. Substitute a literal — <code>Heap.singleton 3 7 3 = some 7</code> — and <code>rfl</code> works, because <code>Nat.decEq 3 3</code> does compute.",
      "variants": "Look up a different location: <code>Heap.singleton l v x</code> for an arbitrary <code>x</code> is not <code>some v</code>, and is not provable at all without knowing how <code>x</code> relates to <code>l</code>. That is the next exercise. Replace <code>Heap.singleton</code> by <code>Heap.write h</code> and you get <code>write_same</code>, whose proof is this one with a single identifier changed — <code>simp [Heap.write]</code>: the two definitions differ only in the else-branch, and at <code>l</code> the else-branch is discarded."
    },
    {
      "t": "ex",
      "id": "m1-2",
      "name": "singleton_other",
      "hard": false,
      "why": "This is the lemma that says the singleton heap really is a singleton: everywhere except <code>l</code> it is undefined.",
      "setup": "You are handed the disequality as a hypothesis <code>hne : x ≠ l</code>. Note which way round it is stated — that is the content of the pitfall below.",
      "goal": "theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.singleton l v x = none",
      "hints": [
        "Same first move as before: unfold, and the goal becomes an <code>if</code> whose condition is <code>x = l</code>. This time <code>simp</code> cannot decide the condition on its own — but you have a hypothesis that decides it. How do you hand a hypothesis to <code>simp</code>?",
        "Put it in the brackets alongside the definition: <code>simp [Heap.singleton, hne]</code>. A hypothesis of the form <code>a ≠ b</code> becomes the rewrite <code>(a = b) ↦ False</code>.",
        "<code>simp [Heap.singleton, hne]</code>."
      ],
      "sol": "theorem singleton_other (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.singleton l v x = none := by\n  simp [Heap.singleton, hne]",
      "expl": "Same shape as <code>update_other</code>. Watch the direction of <code>hne</code>: it is <code>x ≠ l</code>, matching the <code>if x = l</code> in the definition.",
      "walk": [
        {
          "tac": "simp [Heap.singleton, hne]",
          "h": "<code>Heap.singleton</code> unfolds the goal to <code>(if x = l then some v else none) = none</code>; <code>hne</code> rewrites the condition <code>x = l</code> to <code>False</code>; <code>↓reduceIte</code> then takes the else-branch, leaving <code>none = none</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "singleton_other, unfolded",
          "start": "l x : Loc\nv : Val\nhne : x ≠ l\n⊢ Heap.singleton l v x = none",
          "steps": [
            {
              "tac": "unfold Heap.singleton",
              "state": "l x : Loc\nv : Val\nhne : x ≠ l\n⊢ (if x = l then some v else none) = none",
              "h": "Identical to the previous exercise except that the condition is now <code>x = l</code> with <code>x</code> a variable independent of <code>l</code>. Nothing decides it but <code>hne</code>."
            },
            {
              "tac": "rw [if_neg hne]",
              "state": "No goals.",
              "h": "The explicit form of what <code>simp</code> does. <code>if_neg : ¬c → (if c then t else e) = e</code>, so <code>if_neg hne</code> is literally the rewrite that selects the else-branch; the remaining <code>none = none</code> is closed by <code>rw</code>'s automatic <code>rfl</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "hne : x ≠ l — fires",
            "kind": "good",
            "h": "The hypothesis matches the <code>if</code> condition <code>x = l</code> exactly, so <code>simp</code> can rewrite it to <code>False</code> and the proof closes.",
            "src": "simp [Heap.singleton, hne]"
          },
          "right": {
            "t": "hne : l ≠ x — does not fire",
            "kind": "bad",
            "h": "<code>Ne</code> is not symmetric as a <i>term</i>: <code>l ≠ x</code> unfolds to <code>l = x → False</code>, and there is no <code>l = x</code> anywhere in the goal. <code>simp</code> silently ignores the hypothesis and leaves you with the undischarged condition, plus a linter warning that the argument was unused. The repair is the second line: <code>hne.symm</code> is <code>Ne.symm hne : x ≠ l</code>, which does match.",
            "src": "simp [Heap.singleton, hne]        -- stalls\nsimp [Heap.singleton, hne.symm]   -- closes"
          }
        },
        {
          "t": "state",
          "src": "error: unsolved goals\nl x : Loc\nv : Val\nhne : l ≠ x\n⊢ ¬x = l\n\nwarning: This simp argument is unused:\n  hne",
          "cap": "What Lean says when the disequality is stated the wrong way round. Two separate diagnostics, quoted without their file positions; the linter also prints a Hint showing the argument struck out, and a note about how to disable it."
        }
      ],
      "pitfall": "Stating the hypothesis as <code>l ≠ x</code> instead of <code>x ≠ l</code>. It is the same mathematical fact and it will not work: <code>simp</code> matches syntactically, finds no <code>l = x</code> in the goal, discards the hint, and leaves you staring at <code>⊢ ¬x = l</code> with a warning that your argument was unused. The fix is one token — <code>hne.symm</code>, or equivalently <code>Ne.symm hne</code>. You will hit this every time you use this lemma from a context where the disequality arrived in the other orientation, which in M2 is most of the time.",
      "variants": "Drop <code>hne</code> and the statement is false at <code>x = l</code>, where the left side is <code>some v</code>. Lean shows you exactly this if you try: <code>simp [Heap.singleton]</code> reduces the goal to <code>⊢ ¬x = l</code>, i.e. it has done all the work and handed back precisely the missing hypothesis. That is a general and useful habit of <code>simp</code> — when it fails, what remains is often the side condition you forgot."
    },
    {
      "t": "ex",
      "id": "m1-3",
      "name": "write_same / write_other",
      "hard": false,
      "why": "Together these two <i>characterise</i> write: it is the unique heap agreeing with <code>some v</code> at <code>l</code> and with <code>h</code> everywhere else. From here on, any proof that needs to know what <code>Heap.write h l v</code> does at a location rewrites with one of these two and never unfolds anything. That is the difference between a three-line proof of the write rule in M7 and a thirty-line one.",
      "setup": "Two theorems, proved independently. Nothing from the previous exercises is needed.",
      "goal": "theorem write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.write h l v l = some v\n\ntheorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.write h l v x = h x",
      "hints": [
        "These are <code>singleton_same</code> and <code>singleton_other</code> with a different else-branch. Nothing else has changed, so nothing else in the proof changes.",
        "First one: <code>simp [Heap.write]</code>. Second one: you need the disequality in the simp set as well.",
        "<code>simp [Heap.write]</code> and <code>simp [Heap.write, hne]</code>."
      ],
      "sol": "theorem write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.write h l v l = some v := by\n  simp [Heap.write]\n\ntheorem write_other (h : Heap) (l x : Loc) (v : Val) (hne : x ≠ l) :\n    Heap.write h l v x = h x := by\n  simp [Heap.write, hne]",
      "expl": "Both proofs are the corresponding singleton proof with <code>Heap.singleton</code> replaced by <code>Heap.write</code>. In <code>write_same</code> the else-branch <code>h l</code> is discarded by the <code>if</code>, so the presence of <code>h</code> costs nothing; in <code>write_other</code> the then-branch is discarded and what survives is <code>h x</code>, which is the right-hand side.",
      "walk": [
        {
          "tac": "simp [Heap.write]",
          "h": "For <code>write_same</code>. Unfolds to <code>(if l = l then some v else h l) = some v</code>, decides <code>l = l</code>, discards the else-branch, closes by reflexivity. The heap <code>h</code> never enters the argument."
        },
        {
          "tac": "simp [Heap.write, hne]",
          "h": "For <code>write_other</code>. Unfolds to <code>(if x = l then some v else h x) = h x</code>, uses <code>hne</code> to make the condition <code>False</code>, takes the else-branch, and the goal becomes <code>h x = h x</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "write_same",
          "start": "h : Heap\nl : Loc\nv : Val\n⊢ h.write l v l = some v",
          "steps": [
            {
              "tac": "unfold Heap.write",
              "state": "h : Heap\nl : Loc\nv : Val\n⊢ (if l = l then some v else h l) = some v",
              "h": "Note <code>h.write l v l</code> in the starting goal — the first three arguments are <code>write</code>'s, the fourth is the location being looked up. Reading that fourth argument correctly is most of what it takes to follow these proofs."
            },
            {
              "tac": "simp",
              "state": "No goals.",
              "h": "<code>l = l</code> is decided, the else-branch <code>h l</code> is discarded unexamined."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "write_other",
          "start": "h : Heap\nl x : Loc\nv : Val\nhne : x ≠ l\n⊢ h.write l v x = h x",
          "steps": [
            {
              "tac": "unfold Heap.write",
              "state": "h : Heap\nl x : Loc\nv : Val\nhne : x ≠ l\n⊢ (if x = l then some v else h x) = h x",
              "h": "The goal is now visibly “the else-branch is the answer”, which is what <code>hne</code> will license."
            },
            {
              "tac": "rw [if_neg hne]",
              "state": "No goals.",
              "h": "<code>if_neg hne</code> rewrites the whole <code>if</code> to <code>h x</code>; the resulting <code>h x = h x</code> is closed by <code>rw</code>'s trailing <code>rfl</code>. <code>simp [Heap.write, hne]</code> does the same thing in one step."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "It is worth knowing what these two lemmas <i>say</i> in the language of the rest of the course. <code>write_same</code> is read-after-write on the cell you just wrote. <code>write_other</code> is the statement that a write is <b>invisible</b> off its own location — that is the seed of locality, and in M8 it is what lets a frame survive a write."
        }
      ],
      "pitfall": "Forgetting <code>hne</code> in <code>write_other</code>. What comes back is not the goal you started with: <code>simp [Heap.write]</code> leaves <code>⊢ x = l → some v = h x</code>, because <code>simp</code> has already applied the library lemma <code>ite_eq_right_iff : (if c then a else b) = b ↔ (c → a = b)</code>. Compare with <code>singleton_other</code>, where the same omission leaves the tidier <code>⊢ ¬x = l</code> — there the then-branch <code>some v</code> and the right-hand side <code>none</code> are distinct constructors, so <code>reduceCtorEq</code> can turn <code>some v = none</code> into <code>False</code> and <code>simp</code> can go one step further. Here <code>h x</code> is an opaque application and there is nothing more to say about it. Two similar goals, two different residues; read what is actually left rather than assuming.",
      "variants": "Reverse the roles and ask for <code>Heap.write h l v x = some v</code> without <code>x = l</code>: false, and false at every <code>x</code> where <code>h x</code> is anything other than <code>some v</code>. Drop <code>hne</code> from <code>write_other</code> and it fails exactly at <code>x = l</code> for every heap with <code>h l ≠ some v</code> — in particular for <code>h = Heap.empty</code>, where the two sides are <code>some v</code> and <code>none</code>."
    },
    {
      "t": "ex",
      "id": "m1-4",
      "name": "erase_same / erase_other",
      "hard": false,
      "why": "The same characterisation for deallocation: <code>Heap.erase h l</code> is the unique heap undefined at <code>l</code> and equal to <code>h</code> elsewhere. These are the two rewrites behind the free rule in M7, and behind every step of symbolic execution that removes a cell in M9.",
      "setup": "Note that <code>erase_same</code> takes no value argument and <code>erase_other</code> takes no <code>v</code> at all: erasing does not care what was there.",
      "goal": "theorem erase_same (h : Heap) (l : Loc) :\n    Heap.erase h l l = none\n\ntheorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :\n    Heap.erase h l x = h x",
      "hints": [
        "<code>Heap.erase</code> is <code>Heap.write</code> with <code>none</code> in the then-branch. Take the previous pair of proofs and change one identifier.",
        "<code>simp [Heap.erase]</code> and <code>simp [Heap.erase, hne]</code>.",
        "Identical to the previous pair — that is not a hint about the answer, it is the answer."
      ],
      "sol": "theorem erase_same (h : Heap) (l : Loc) :\n    Heap.erase h l l = none := by\n  simp [Heap.erase]\n\ntheorem erase_other (h : Heap) (l x : Loc) (hne : x ≠ l) :\n    Heap.erase h l x = h x := by\n  simp [Heap.erase, hne]",
      "expl": "Structurally identical to <code>write_same</code> / <code>write_other</code>. The repetition is deliberate: <code>write</code> and <code>erase</code> are the same construction with a different then-branch, and every lemma about one has a mirror about the other. Later chapters will exploit that by proving a fact about writes and reading off the fact about erases.",
      "walk": [
        {
          "tac": "simp [Heap.erase]",
          "h": "For <code>erase_same</code>. Unfolds to <code>(if l = l then none else h l) = none</code>, decides the condition, keeps the then-branch <code>none</code>."
        },
        {
          "tac": "simp [Heap.erase, hne]",
          "h": "For <code>erase_other</code>. Unfolds to <code>(if x = l then none else h x) = h x</code>; <code>hne</code> makes the condition <code>False</code> and the else-branch <code>h x</code> survives."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "erase_same",
          "start": "h : Heap\nl : Loc\n⊢ h.erase l l = none",
          "steps": [
            {
              "tac": "unfold Heap.erase",
              "state": "h : Heap\nl : Loc\n⊢ (if l = l then none else h l) = none",
              "h": "Compare with <code>write_same</code>: only <code>some v</code> has become <code>none</code>."
            },
            {
              "tac": "simp",
              "state": "No goals.",
              "h": "As before."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "erase_other",
          "start": "h : Heap\nl x : Loc\nhne : x ≠ l\n⊢ h.erase l x = h x",
          "steps": [
            {
              "tac": "unfold Heap.erase",
              "state": "h : Heap\nl x : Loc\nhne : x ≠ l\n⊢ (if x = l then none else h x) = h x",
              "h": "The shape you have now seen four times."
            },
            {
              "tac": "rw [if_neg hne]",
              "state": "No goals.",
              "h": "Explicit version of <code>simp [Heap.erase, hne]</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "Six lemmas done, and they are the whole interface. The claim in the section header — <i>never unfold <code>Heap.write</code> again</i> — is worth taking seriously, with one qualification: it starts applying at the end of <i>this</i> chapter, not now. The four remaining exercises are equations between heaps rather than lookups, and they are still proved from the definitions, because that is what it takes to establish them. From M2 onwards, a proof that unfolds <code>Heap.write</code> is a proof that has dropped below the interface, and it is worth stopping to ask which of these eleven equations you actually needed."
        }
      ],
      "pitfall": "Omitting <code>hne</code> in <code>erase_other</code> leaves <code>⊢ x = l → none = h x</code>, which reads as though something is deeply wrong. It is the same phenomenon as in <code>write_other</code>: <code>simp</code> has turned <code>(if c then none else h x) = h x</code> into the implication <code>c → none = h x</code> and is waiting for you to refute <code>c</code>. Adding <code>hne</code> to the simp set does exactly that.",
      "variants": "There is no <code>erase</code> analogue of <code>write_same</code> that mentions the erased value, because there is nothing to mention — and that asymmetry is real content, not an accident of the encoding. It is why <code>erase_write_same</code> (two exercises on) is true: everything you wrote is forgotten. Note also that <code>erase_same</code> holds for <i>every</i> <code>h</code>, including heaps where <code>l</code> was never allocated; <code>Heap.erase</code> is not a partial operation and it does not require ownership. Ownership is imposed later, by the precondition of the free rule, not by the definition."
    },
    {
      "t": "sec",
      "s": "Exercises · algebraic laws"
    },
    {
      "t": "p",
      "h": "The four exercises above were about a single lookup. The four below are equations between <i>heaps</i>, and every one of them is proved by the same three tactics. If you learn one thing mechanically from this chapter, learn this pattern; you will type it several dozen more times before M13."
    },
    {
      "t": "ex",
      "id": "m1-5",
      "name": "write_shadow",
      "hard": false,
      "why": "Writing twice to the same cell: only the last write is observable. This is what makes the assignment axiom sound.",
      "setup": "The first equation between heaps rather than between lookups. You may use anything proved so far, but you will not need to — the proof works directly from the definition.",
      "hints": [
        "The two sides are heaps, that is, functions. What is the standard way to prove two functions equal? (M0, third technique.)",
        "<code>funext x</code>. Now you have an equation at an arbitrary location <code>x</code>, and both sides are <code>if</code>-expressions whose condition <code>x = l</code> nobody has decided for you. Decide it yourself.",
        "<code>funext x</code>, then <code>by_cases hx : x = l</code>, then <code>simp [Heap.write, hx]</code> in each branch. Both branches take the same tactic, so you can join them with <code>&lt;;&gt;</code>."
      ],
      "goal": "theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :\n    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂",
      "sol": "theorem write_shadow (h : Heap) (l : Loc) (v₁ v₂ : Val) :\n    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, hx]",
      "expl": "The pattern <code>funext</code> → <code>by_cases</code> → <code>simp</code> is now permanent furniture; you will use it for every heap identity in this milestone and the next.",
      "walk": [
        {
          "tac": "funext x",
          "h": "Replaces the goal <code>f = g</code> by <code>f x = g x</code> for a fresh <code>x : Loc</code>. This is the only step that has anything to do with heaps being functions; after it, the goal is an ordinary equation in <code>Option Val</code>."
        },
        {
          "tac": "by_cases hx : x = l <;> simp [Heap.write, hx]",
          "h": "<code>by_cases hx : x = l</code> splits into two goals, labelled <code>case pos</code> with <code>hx : x = l</code> and <code>case neg</code> with <code>hx : ¬x = l</code>. The combinator <code>&lt;;&gt;</code> then runs <code>simp [Heap.write, hx]</code> on <i>both</i> of them. In the positive branch <code>hx</code> rewrites <code>x</code> to <code>l</code> and every condition becomes <code>True</code>, so both sides reduce to <code>some v₂</code>; in the negative branch every condition becomes <code>False</code>, so both sides reduce to <code>h x</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "write_shadow, tactic by tactic",
          "start": "h : Heap\nl : Loc\nv₁ v₂ : Val\n⊢ (h.write l v₁).write l v₂ = h.write l v₂",
          "steps": [
            {
              "tac": "funext x",
              "state": "h : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\n⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x",
              "h": "One new hypothesis, <code>x : Loc</code>, and one extra argument on each side of the equation. Nothing else changed. Note that this is now an equation in <code>Option Val</code>, so all the machinery of the previous four exercises applies."
            },
            {
              "tac": "by_cases hx : x = l",
              "state": "case pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x\n\ncase neg\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : ¬x = l\n⊢ (h.write l v₁).write l v₂ x = h.write l v₂ x",
              "h": "Two goals, identical except for the new hypothesis. <code>case pos</code> and <code>case neg</code> are Lean's names for the branches, not something you wrote. The negative hypothesis prints as <code>¬x = l</code>, which is the same thing as <code>x ≠ l</code> — <code>Ne</code> is notation for exactly this."
            },
            {
              "tac": "simp only [Heap.write]   (positive branch)",
              "state": "case pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then some v₂ else if x = l then some v₁ else h x) = if x = l then some v₂ else h x",
              "h": "Both writes unfolded. The nesting on the left is the two writes: outer condition first. This intermediate state is not in the solution — the single <code>simp</code> does it and the next step in one — but it is what you would see if you stopped here."
            },
            {
              "tac": "simp only [hx]           (positive branch)",
              "state": "case pos\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : x = l\n⊢ (if True then some v₂ else if True then some v₁ else h l) = if True then some v₂ else h l",
              "h": "Here is the thing worth seeing: <code>hx : x = l</code> is used as a <i>rewrite</i>, replacing <code>x</code> by <code>l</code> throughout, after which <code>l = l</code> collapses to <code>True</code>. The inner <code>if</code> — the earlier write, holding <code>v₁</code> — is still there but is now unreachable. It is thrown away when <code>↓reduceIte</code> fires, and that discarding is the whole theorem."
            },
            {
              "tac": "simp only [Heap.write, hx]   (negative branch)",
              "state": "case neg\nh : Heap\nl : Loc\nv₁ v₂ : Val\nx : Loc\nhx : ¬x = l\n⊢ (if False then some v₂ else if False then some v₁ else h x) = if False then some v₂ else h x",
              "h": "The mirror image: <code>hx</code> is a negation, so it rewrites the condition to <code>False</code>, both <code>if</code>s take their else-branches, and both sides become <code>h x</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "The attempt that does not work",
            "kind": "bad",
            "h": "Straight to <code>simp</code> without going pointwise. Lean answers <code>`simp` made no progress</code>. The reason is precise: the equation for <code>Heap.write</code> only matches an <i>applied</i> occurrence, and here <code>Heap.write h l v₁</code> is not applied to a location. There is nothing for the rewrite to grab.",
            "src": "example (h : Heap) (l : Loc) (v₁ v₂ : Val) :\n    Heap.write (Heap.write h l v₁) l v₂ = Heap.write h l v₂ := by\n  simp [Heap.write]"
          },
          "right": {
            "t": "Why funext is not optional",
            "h": "<code>funext x</code> supplies the missing argument. It is not a bookkeeping step you could skip with a cleverer tactic: without it there is no location at which to compare the two heaps, and no <code>if</code> to collapse. If you prefer to see the lambdas, <code>unfold Heap.write</code> does work unapplied and leaves <code>⊢ (fun x => if x = l then some v₂ else if x = l then some v₁ else h x) = fun x => if x = l then some v₂ else h x</code> — at which point you still need <code>funext</code>.",
            "src": "funext x\nby_cases hx : x = l <;> simp [Heap.write, hx]"
          }
        },
        {
          "t": "steps",
          "title": "The argument underneath, in one sentence per region",
          "items": [
            {
              "k": "At l",
              "h": "The outer write answers <code>some v₂</code> and never consults the inner one. On the right, the single write answers <code>some v₂</code>. Equal."
            },
            {
              "k": "Away from l",
              "h": "Neither write applies, so both sides defer to <code>h</code>. Equal."
            },
            {
              "k": "There is no third region",
              "h": "Which is why two cases suffice, and why this proof — unlike <code>write_comm</code> — needs no disequality hypothesis at all."
            }
          ]
        }
      ],
      "pitfall": "Reaching for <code>simp</code> or <code>rfl</code> before <code>funext</code>. <code>rfl</code> reports <code>Tactic `rfl` failed: The left-hand side (h.write l v₁).write l v₂ is not definitionally equal to the right-hand side h.write l v₂</code> — the two sides are lambdas whose bodies get no further, because going further would mean deciding <code>x = l</code> for a bound variable. <code>simp [Heap.write]</code> fails with <code>`simp` made no progress</code> for the separate reason given above. Both failures point at the same missing step. A second, quieter trap: writing <code>by_cases hx : l = x</code> with the arguments the other way round. It splits the goal just the same, but then <code>simp [Heap.write, hx]</code> has a hypothesis about <code>l = x</code> and a goal about <code>x = l</code>, and the negative branch will not close.",
      "variants": "Change the second write to a different location and the statement becomes false: <code>Heap.write (Heap.write h l v₁) l' v₂</code> keeps <code>v₁</code> at <code>l</code>, so it cannot equal <code>Heap.write h l' v₂</code> unless <code>h l = some v₁</code> already. The correct statement about two locations is <code>write_comm</code>, three exercises on, and it needs <code>l ≠ l'</code>. Swap the two writes on the left and the right-hand side has to move with them: <code>Heap.write (Heap.write h l v₂) l v₁</code> is <code>Heap.write h l v₁</code>, not <code>Heap.write h l v₂</code>. The value that survives is always the outer, later one — which is the whole content of the lemma, and the reason it is the assignment axiom rather than a curiosity."
    },
    {
      "t": "ex",
      "id": "m1-6",
      "name": "erase_write_same",
      "hard": false,
      "why": "If you are going to delete a cell, it does not matter what you put in it first. This is exactly the lemma that makes <code>write; free</code> equal to <code>free</code>.",
      "setup": "Same pattern as <code>write_shadow</code>, but now the two operations are different, so both definitions have to go into the <code>simp</code> set.",
      "hints": [
        "Same three tactics as the previous exercise. The only question is what to put in the brackets.",
        "The goal mentions both <code>Heap.erase</code> and <code>Heap.write</code>, so <code>simp</code> needs both names: <code>simp [Heap.erase, Heap.write, hx]</code>.",
        "<code>funext x</code>, then <code>by_cases hx : x = l &lt;;&gt; simp [Heap.erase, Heap.write, hx]</code>."
      ],
      "goal": "theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.erase (Heap.write h l v) l = Heap.erase h l",
      "sol": "theorem erase_write_same (h : Heap) (l : Loc) (v : Val) :\n    Heap.erase (Heap.write h l v) l = Heap.erase h l := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]",
      "expl": "The <code>erase</code> in front discards the then-branch of the write, so the value <code>v</code> is unreachable at <code>l</code>; away from <code>l</code> neither operation does anything. Two regions, two lines.",
      "walk": [
        {
          "tac": "funext x",
          "h": "Both sides are heaps; go pointwise. The goal becomes <code>(h.write l v).erase l x = h.erase l x</code>."
        },
        {
          "tac": "by_cases hx : x = l <;> simp [Heap.erase, Heap.write, hx]",
          "h": "Splits at <code>x = l</code> and closes both branches. In the positive branch both sides are <code>none</code> — the erase wins on the left, and there is nothing else to say on the right. In the negative branch neither operation fires and both sides are <code>h x</code>. Note that <code>Heap.write</code> must be in the simp set even though it plays no role in the answer: <code>simp</code> has to unfold it before it can see that the value is discarded."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "erase_write_same, tactic by tactic",
          "start": "h : Heap\nl : Loc\nv : Val\n⊢ (h.write l v).erase l = h.erase l",
          "steps": [
            {
              "tac": "funext x",
              "state": "h : Heap\nl : Loc\nv : Val\nx : Loc\n⊢ (h.write l v).erase l x = h.erase l x",
              "h": "Read the left-hand side outside-in: erase, at <code>l</code>, of the write, evaluated at <code>x</code>."
            },
            {
              "tac": "by_cases hx : x = l",
              "state": "case pos\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ (h.write l v).erase l x = h.erase l x\n\ncase neg\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ (h.write l v).erase l x = h.erase l x",
              "h": "Two goals again, with the same shape as <code>write_shadow</code>."
            },
            {
              "tac": "unfold Heap.erase Heap.write   (positive branch)",
              "state": "case pos\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then none else if x = l then some v else h x) = if x = l then none else h x",
              "h": "Here is the point of the whole lemma, visible in the syntax: <code>some v</code> sits in the else-branch of an <code>if</code> whose then-branch is <code>none</code> and whose condition is about to be <code>True</code>. It is dead code."
            },
            {
              "tac": "unfold Heap.erase Heap.write   (negative branch)",
              "state": "case neg\nh : Heap\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ (if x = l then none else if x = l then some v else h x) = if x = l then none else h x",
              "h": "The same goal with a negated hypothesis. Every condition becomes <code>False</code>, every <code>if</code> takes its else-branch, and both sides land on <code>h x</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "The operational reading is worth stating because you will use it in M9: in a program, <code>[l] := v; free l</code> has the same effect on the heap as <code>free l</code> alone. Any optimisation that deletes a store to a location that is about to be freed is justified by this one equation."
        }
      ],
      "pitfall": "Leaving <code>Heap.write</code> out of the simp set on the grounds that the write “does not matter”. It does not matter to the <i>answer</i>, but <code>simp</code> cannot know that until it has unfolded the definition and looked. With only <code>[Heap.erase, hx]</code> the positive branch closes anyway — there the erase alone decides everything — and the negative branch stalls at <code>⊢ h.write l v x = h x</code>, which is <code>write_other</code>, true but unproved. Note the shape of that residue: it is a lemma you already have, so <code>rw [write_other _ _ _ _ hx]</code> also finishes the job — four underscores for <code>write_other</code>'s four value arguments <code>h</code>, <code>l</code>, <code>x</code>, <code>v</code>, which Lean recovers by matching the lemma's left-hand side against the goal, and then <code>hx</code> for the disequality, which it cannot recover and you must supply. Adding the definition to the simp set is simply shorter.",
      "variants": "Erase at a <i>different</i> location and the statement is false: <code>Heap.erase (Heap.write h l v) l'</code> still holds <code>v</code> at <code>l</code>, whereas <code>Heap.erase h l'</code> holds whatever <code>h</code> held. The true statement in that case is a commutation law, <code>erase (write h l v) l' = write (erase h l') l v</code> for <code>l ≠ l'</code>, which is the erase-analogue of the next exercise and is proved the same way. Reverse the order — <code>Heap.write (Heap.erase h l) l v</code> — and you get <code>Heap.write h l v</code>, since the write overrides the hole it just made."
    },
    {
      "t": "ex",
      "id": "m1-7",
      "name": "write_comm",
      "hard": false,
      "why": "Writes to <i>different</i> cells commute. This is the germ of the frame rule: the reason a command can be moved past an unrelated piece of memory is that their effects commute.",
      "setup": "This is the one exercise where you should deliberately not use <code>simp</code>. The proof drives every <code>if</code> by hand with <code>if_pos</code> and <code>if_neg</code>, so you can watch which branch collapses where — and, more to the point, so you can see the single line where <code>hne</code> is consumed. It is the same proof as <code>update_comm</code> in M0, with <code>Option Val</code> in the codomain.",
      "hints": [
        "Go pointwise as usual, then <code>unfold Heap.write</code> rather than putting it in a simp set: you want to see the nested <code>if</code>s.",
        "There are three regions, not two: <code>x = l₁</code>, <code>x = l₂</code>, and neither. Nest a second <code>by_cases</code> inside the negative branch of the first.",
        "In the branch <code>x = l₁</code> you also need <code>x ≠ l₂</code>, and it does not come for free — derive it: <code>have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne</code>. That is the only place <code>hne</code> is used in the whole proof.",
        "Then it is bookkeeping: in each branch, <code>rw [if_pos …]</code> / <code>rw [if_neg …]</code> until both sides are the same term. Each rewrite fires on the outermost <code>if</code> whose condition it matches, and <code>rw</code> closes the goal with <code>rfl</code> as soon as the two sides agree."
      ],
      "goal": "theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.write (Heap.write h l₁ v₁) l₂ v₂ =\n    Heap.write (Heap.write h l₂ v₂) l₁ v₁",
      "sol": "theorem write_comm (h : Heap) (l₁ l₂ : Loc) (v₁ v₂ : Val) (hne : l₁ ≠ l₂) :\n    Heap.write (Heap.write h l₁ v₁) l₂ v₂ = Heap.write (Heap.write h l₂ v₂) l₁ v₁ := by\n  funext x\n  unfold Heap.write\n  by_cases hx₁ : x = l₁\n  · have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne\n    rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]\n  · by_cases hx₂ : x = l₂\n    · rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]\n    · rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]",
      "expl": "In the case <code>x = l₁</code> we <i>derive</i> <code>x ≠ l₂</code> from <code>hne</code>, and that is the only use of the hypothesis. The other two cases never need it. If you remove <code>hne</code> the theorem is false exactly at <code>x = l₁ = l₂</code>, where the two sides disagree (<code>v₂</code> versus <code>v₁</code>).",
      "walk": [
        {
          "tac": "funext x",
          "h": "Pointwise, as always. The goal becomes <code>(h.write l₁ v₁).write l₂ v₂ x = (h.write l₂ v₂).write l₁ v₁ x</code>."
        },
        {
          "tac": "unfold Heap.write",
          "h": "Deliberately <code>unfold</code> rather than <code>simp [Heap.write]</code>. Both sides become two nested <code>if</code>s, and now every subsequent step is visible. Note the orders: on the left the outer test is <code>x = l₂</code>, on the right it is <code>x = l₁</code>."
        },
        {
          "tac": "by_cases hx₁ : x = l₁",
          "h": "The first of the three regions. Positive branch first."
        },
        {
          "tac": "have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne",
          "h": "The load-bearing line. <code>rw [hx₁]</code> rewrites the goal <code>x ≠ l₂</code> into <code>l₁ ≠ l₂</code> using <code>hx₁ : x = l₁</code>, and <code>exact hne</code> supplies it. This is the <i>only</i> consumption of <code>hne</code> anywhere in the proof: non-aliasing enters here and nowhere else."
        },
        {
          "tac": "rw [if_neg hx₂, if_pos hx₁, if_pos hx₁]",
          "h": "Three rewrites, in order: kill the outer <code>if</code> on the left (its condition <code>x = l₂</code> is false), then collapse the inner <code>if</code> on the left to <code>some v₁</code>, then collapse the outer <code>if</code> on the right to <code>some v₁</code>. The two sides now agree and <code>rw</code>'s trailing <code>rfl</code> closes the goal."
        },
        {
          "tac": "by_cases hx₂ : x = l₂",
          "h": "Inside the branch where <code>x ≠ l₁</code>, split again. Note that here <code>hx₂</code> is a fresh hypothesis, not the derived one from the other branch."
        },
        {
          "tac": "rw [if_pos hx₂, if_neg hx₁, if_pos hx₂]",
          "h": "The mirror of the first branch: the left side collapses to <code>some v₂</code> straight away; on the right the outer <code>if</code> fails and the inner one succeeds."
        },
        {
          "tac": "rw [if_neg hx₂, if_neg hx₁, if_neg hx₁, if_neg hx₂]",
          "h": "Four rewrites because there are four <code>if</code>s and none of them fire: two on the left, two on the right, all taking their else-branch, until both sides are literally <code>h x</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "write_comm — the branch where hne is used",
          "start": "h : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\n⊢ (h.write l₁ v₁).write l₂ v₂ = (h.write l₂ v₂).write l₁ v₁",
          "steps": [
            {
              "tac": "funext x",
              "state": "h : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\n⊢ (h.write l₁ v₁).write l₂ v₂ x = (h.write l₂ v₂).write l₁ v₁ x",
              "h": "As always."
            },
            {
              "tac": "unfold Heap.write",
              "state": "h : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\n⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =\n    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
              "h": "Lean wraps the goal over two lines. Read it as: on the left, test <code>l₂</code> first (the outer, later write); on the right, test <code>l₁</code> first. The theorem says these two decision trees agree, and the only place they could disagree is where both tests succeed."
            },
            {
              "tac": "by_cases hx₁ : x = l₁ · have hx₂ : x ≠ l₂ := by rw [hx₁]; exact hne",
              "state": "case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : x ≠ l₂\n⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =\n    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
              "h": "The goal is unchanged; what changed is the context, which now contains <code>hx₂ : x ≠ l₂</code>. That hypothesis is the entire mathematical content of the theorem. Everything after this is rewriting."
            },
            {
              "tac": "rw [if_neg hx₂]",
              "state": "case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : x ≠ l₂\n⊢ (if x = l₁ then some v₁ else h x) = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
              "h": "Only the left side moved. The right side also contains an <code>if</code> on <code>x = l₂</code>, but with a different else-branch, so it is a different term and <code>rw</code> did not touch it — <code>rw</code> rewrites all occurrences of the term it first matched, not all occurrences of the pattern."
            },
            {
              "tac": "rw [if_pos hx₁]",
              "state": "case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : x ≠ l₂\n⊢ some v₁ = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
              "h": "Left side finished: <code>some v₁</code>. Same reasoning about which occurrence was hit — the two <code>if x = l₁</code> terms differ in their else-branches."
            },
            {
              "tac": "rw [if_pos hx₁]",
              "state": "",
              "h": "The same rewrite again, now the only match is on the right. It produces <code>some v₁ = some v₁</code>, which <code>rw</code> closes automatically with <code>rfl</code> — so this branch ends with no goal and <code>trace_state</code> prints nothing at all."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "write_comm — the other two branches",
          "start": "case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : x = l₂\n⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =\n    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
          "steps": [
            {
              "tac": "rw [if_pos hx₂]",
              "state": "case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : x = l₂\n⊢ some v₂ = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
              "h": "The branch <code>x = l₂</code>. Lean labels it <code>case pos</code> again — the label refers to the innermost <code>by_cases</code>, so <code>case pos</code> appearing twice in one proof is normal and tells you nothing about which split you are in. Read the hypotheses, not the label."
            },
            {
              "tac": "rw [if_neg hx₁]",
              "state": "case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : x = l₂\n⊢ some v₂ = if x = l₂ then some v₂ else h x",
              "h": "The outer test on the right fails, exposing the inner one."
            },
            {
              "tac": "rw [if_pos hx₂]",
              "state": "case neg\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : ¬x = l₂\n⊢ (if x = l₂ then some v₂ else if x = l₁ then some v₁ else h x) =\n    if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
              "h": "That branch closes, and what is displayed is the <i>next</i> goal: the third region, where <code>x</code> is neither location. Note that <code>hne</code> is still sitting in the context, unused and unusable — there is nothing to derive here."
            },
            {
              "tac": "rw [if_neg hx₂, if_neg hx₁]",
              "state": "case neg\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : ¬x = l₂\n⊢ h x = if x = l₁ then some v₁ else if x = l₂ then some v₂ else h x",
              "h": "The left side has collapsed all the way to <code>h x</code>. Two <code>if</code>s remain on the right."
            },
            {
              "tac": "rw [if_neg hx₁]",
              "state": "case neg\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : ¬x = l₂\n⊢ h x = if x = l₂ then some v₂ else h x",
              "h": "This is why <code>if_neg hx₁</code> appears twice in the solution: the first occurrence killed the left side, the second kills the right. Same lemma, different term."
            },
            {
              "tac": "rw [if_neg hx₂]",
              "state": "",
              "h": "<code>h x = h x</code>, closed by the automatic <code>rfl</code>. No goals left."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The three regions",
          "items": [
            {
              "k": "x = l₁",
              "h": "Only the <code>v₁</code>-write is visible. On the left this needs the <code>l₂</code>-test to fail, which is exactly what <code>hne</code> buys. On the right it is immediate."
            },
            {
              "k": "x = l₂",
              "h": "Only the <code>v₂</code>-write is visible. Here the <code>l₁</code>-test failing is given directly by <code>hx₁</code>, so nothing has to be derived."
            },
            {
              "k": "neither",
              "h": "Both sides fall through to <code>h x</code>. Four failing tests, no content."
            }
          ]
        },
        {
          "t": "p",
          "h": "The asymmetry between the first two regions is not an artefact of how the proof was written. In the region <code>x = l₁</code> the outer test on the left is <code>x = l₂</code>, and nothing in the local context refutes it; you must go back to the global hypothesis. In the region <code>x = l₂</code> the outer test on the right is <code>x = l₁</code>, and the branch you are in already tells you it fails. Two regions, one hypothesis, used once."
        },
        {
          "t": "p",
          "h": "Delete <code>hne</code> and the theorem is false; here is the witness, machine-checked. Take <code>l₁ = l₂ = 0</code>, <code>h = Heap.empty</code>, <code>v₁ = 1</code>, <code>v₂ = 2</code>. The two sides disagree at location <code>0</code>."
        },
        {
          "t": "code",
          "tag": "illustration",
          "cap": "Without non-aliasing, the two orders of writing differ — and the difference is visible at a single location.",
          "src": "example :\n    Heap.write (Heap.write Heap.empty 0 1) 0 2 ≠\n    Heap.write (Heap.write Heap.empty 0 2) 0 1 := by\n  intro heq\n  have h0 := congrFun heq 0\n  rw [write_same, write_same] at h0\n  exact absurd h0 (by simp)"
        },
        {
          "t": "state",
          "src": "heq : (Heap.empty.write 0 1).write 0 2 = (Heap.empty.write 0 2).write 0 1\nh0 : some 2 = some 1\n⊢ False",
          "cap": "The context just before the contradiction: h0 says 2 = 1."
        },
        {
          "t": "p",
          "h": "Finally, the goals left by the <code>&lt;;&gt;</code> shortcut described in the pitfall below. Three of the four branches survive, and the third one is the interesting one — the same fact as <code>hne</code>, written the other way round:"
        },
        {
          "t": "state",
          "src": "case pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : x = l₂\n⊢ l₁ = l₂ → v₂ = v₁\n\ncase neg\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : x = l₁\nhx₂ : ¬x = l₂\n⊢ l₁ = l₂ → v₂ = v₁\n\ncase pos\nh : Heap\nl₁ l₂ : Loc\nv₁ v₂ : Val\nhne : l₁ ≠ l₂\nx : Loc\nhx₁ : ¬x = l₁\nhx₂ : x = l₂\n⊢ l₂ = l₁ → v₂ = v₁",
          "cap": "After <code>funext x</code>, then <code>by_cases hx₁ : x = l₁ &lt;;&gt; by_cases hx₂ : x = l₂ &lt;;&gt; simp [Heap.write, hx₁, hx₂]</code>. In each surviving branch <code>simp</code> has reduced the goal to exactly the hypothesis it was missing."
        }
      ],
      "pitfall": "Trying to close everything with <code>funext x</code> followed by <code>by_cases hx₁ : x = l₁ &lt;;&gt; by_cases hx₂ : x = l₂ &lt;;&gt; simp [Heap.write, hx₁, hx₂]</code>. It is tidier and it does not work: one of the four branches closes and three come back with a residue <code>simp</code> cannot discharge, because nothing in the simp set says the two locations differ. Two of them read <code>⊢ l₁ = l₂ → v₂ = v₁</code> and the third reads <code>⊢ l₂ = l₁ → v₂ = v₁</code> — see the goals below. Add <code>hne</code> and the two that match it close; the reversed one survives, because <code>hne : l₁ ≠ l₂</code> does not match <code>l₂ = l₁</code> syntactically. <code>simp [Heap.write, hx₁, hx₂, hne, hne.symm]</code> does finally close all four — the orientation trap from <code>singleton_other</code>, and from <code>update_comm</code> in M0, arriving a third time. The book proof is written the long way not because the short one is impossible but because it hides where the hypothesis is used, and that location is the theorem. A second, smaller trap: stating the hypothesis as <code>hne : l₂ ≠ l₁</code>. Then <code>rw [hx₁]; exact hne</code> does not typecheck, and the fix is <code>exact hne.symm</code>.",
      "variants": "Drop <code>hne</code> and the statement is false exactly at <code>x = l₁ = l₂</code>, where the left side answers <code>some v₂</code> and the right side <code>some v₁</code> — see the counterexample above. Note that it is false only when the <i>values</i> differ too: with <code>v₁ = v₂</code> the statement is true even without <code>hne</code>, which tells you that what the hypothesis really excludes is a write–write conflict, not aliasing as such. Replace one write by an erase and the same law holds by the same three-region argument — <code>Heap.erase (Heap.write h l v) l' = Heap.write (Heap.erase h l') l v</code> for <code>l ≠ l'</code> — and replace both and the disequality becomes unnecessary, because two erases commute even at the same location. The general principle — <i>operations on disjoint footprints commute</i> — is what M8 turns into the frame rule."
    },
    {
      "t": "ex",
      "id": "m1-8",
      "name": "write_singleton / erase_singleton",
      "hard": false,
      "why": "Not in the original syllabus, but you will need both in M7 and they will save you real pain: they are exactly the computations behind the write rule and the free rule.",
      "setup": "Both are the standard three-tactic pattern. The only thing to be careful about is which definitions go into the <code>simp</code> set — and, in the second one, that <code>Heap.empty</code> is a definition too.",
      "hints": [
        "Nothing new. <code>funext x</code>, <code>by_cases hx : x = l</code>, and one <code>simp</code> for both branches.",
        "The simp set must contain every definition that occurs in the goal. For the first: <code>Heap.write</code> and <code>Heap.singleton</code>. For the second, count again — there are three.",
        "<code>simp [Heap.write, Heap.singleton, hx]</code> and <code>simp [Heap.erase, Heap.singleton, Heap.empty, hx]</code>."
      ],
      "goal": "theorem write_singleton (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w\n\ntheorem erase_singleton (l : Loc) (v : Val) :\n    Heap.erase (Heap.singleton l v) l = Heap.empty",
      "sol": "theorem write_singleton (l : Loc) (v w : Val) :\n    Heap.write (Heap.singleton l v) l w = Heap.singleton l w := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]\n\ntheorem erase_singleton (l : Loc) (v : Val) :\n    Heap.erase (Heap.singleton l v) l = Heap.empty := by\n  funext x\n  by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]",
      "expl": "<code>erase_singleton</code> is the entire content of the free rule. Once you have it, <code>hoare_free</code> is three lines.",
      "walk": [
        {
          "tac": "funext x",
          "h": "For <code>write_singleton</code>. Goal becomes <code>(Heap.singleton l v).write l w x = Heap.singleton l w x</code>. Note that the pretty-printer dots the <code>write</code> but not the <code>singleton</code>: dot notation only applies when the first explicit argument has the namespace's type, and <code>singleton</code>'s first argument is a <code>Loc</code>."
        },
        {
          "tac": "by_cases hx : x = l <;> simp [Heap.write, Heap.singleton, hx]",
          "h": "At <code>l</code>: the write overrides, giving <code>some w</code>, and the right side is <code>some w</code>. Off <code>l</code>: the write defers to the singleton, which is <code>none</code>, and the right side is also <code>none</code>. The old value <code>v</code> never survives either branch — which is exactly why this is the write rule."
        },
        {
          "tac": "funext x",
          "h": "For <code>erase_singleton</code>. Goal becomes <code>(Heap.singleton l v).erase l x = Heap.empty x</code>."
        },
        {
          "tac": "by_cases hx : x = l <;> simp [Heap.erase, Heap.singleton, Heap.empty, hx]",
          "h": "At <code>l</code>: erase gives <code>none</code>, and <code>Heap.empty l</code> is <code>none</code>. Off <code>l</code>: the singleton was already <code>none</code>, and so is <code>Heap.empty</code>. Both branches end in <code>none = none</code>. <code>Heap.empty</code> has to be named in the simp set or the right side stays as an unreduced application."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "write_singleton",
          "start": "l : Loc\nv w : Val\n⊢ (Heap.singleton l v).write l w = Heap.singleton l w",
          "steps": [
            {
              "tac": "funext x",
              "state": "l : Loc\nv w : Val\nx : Loc\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x",
              "h": "Pointwise."
            },
            {
              "tac": "by_cases hx : x = l",
              "state": "case pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x\n\ncase neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ (Heap.singleton l v).write l w x = Heap.singleton l w x",
              "h": "Two branches."
            },
            {
              "tac": "unfold Heap.write Heap.singleton   (positive branch)",
              "state": "case pos\nl : Loc\nv w : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then some w else if x = l then some v else none) = if x = l then some w else none",
              "h": "Structurally the same goal as <code>write_shadow</code>'s, with <code>h x</code> replaced by <code>none</code>. Which is the point: <code>write_singleton</code> <i>is</i> <code>write_shadow</code> for the special heap whose default is <code>none</code>."
            },
            {
              "tac": "unfold Heap.write Heap.singleton   (negative branch)",
              "state": "case neg\nl : Loc\nv w : Val\nx : Loc\nhx : ¬x = l\n⊢ (if x = l then some w else if x = l then some v else none) = if x = l then some w else none",
              "h": "Every condition becomes <code>False</code>; both sides are <code>none</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "erase_singleton",
          "start": "l : Loc\nv : Val\n⊢ (Heap.singleton l v).erase l = Heap.empty",
          "steps": [
            {
              "tac": "funext x",
              "state": "l : Loc\nv : Val\nx : Loc\n⊢ (Heap.singleton l v).erase l x = Heap.empty x",
              "h": "Note <code>Heap.empty x</code> on the right — <code>Heap.empty</code> is a function, and <code>funext</code> has applied it to <code>x</code> like everything else. It will not reduce to <code>none</code> until you name it in the simp set."
            },
            {
              "tac": "by_cases hx : x = l",
              "state": "case pos\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ (Heap.singleton l v).erase l x = Heap.empty x\n\ncase neg\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ (Heap.singleton l v).erase l x = Heap.empty x",
              "h": "Two branches, as usual."
            },
            {
              "tac": "unfold Heap.erase Heap.singleton Heap.empty   (positive branch)",
              "state": "case pos\nl : Loc\nv : Val\nx : Loc\nhx : x = l\n⊢ (if x = l then none else if x = l then some v else none) = none",
              "h": "With <code>Heap.empty</code> unfolded the right side is the constant <code>none</code>, and both branches of the left <code>if</code> lead to <code>none</code> as well. The lemma is nearly trivial once you can see it — the work was getting the definitions out of the way."
            },
            {
              "tac": "unfold Heap.erase Heap.singleton Heap.empty   (negative branch)",
              "state": "case neg\nl : Loc\nv : Val\nx : Loc\nhx : ¬x = l\n⊢ (if x = l then none else if x = l then some v else none) = none",
              "h": "Same goal, negated hypothesis, same answer."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "p",
          "h": "Read the two statements as specifications and they are the small-footprint rules of M7, before any Hoare machinery exists. <code>write_singleton</code>: starting from a heap that is <i>exactly</i> <code>l ↦ v</code>, a write leaves a heap that is exactly <code>l ↦ w</code>. <code>erase_singleton</code>: starting from exactly <code>l ↦ v</code>, a free leaves exactly the empty heap. Both are false under the inexact reading of points-to, which is the concrete cash value of the callout at the top of this chapter."
        }
      ],
      "pitfall": "Leaving <code>Heap.empty</code> out of the <code>erase_singleton</code> simp set. The proof gets tantalisingly close and then stops with <code>⊢ none = Heap.empty l</code> in the positive branch and <code>⊢ none = Heap.empty x</code> in the negative one — both of which are <i>true</i>, and neither of which <code>simp</code> will prove, because <code>Heap.empty</code> is an opaque constant until you name it. The same trap catches <code>Heap.singleton</code> in the first theorem: with only <code>[Heap.write, hx]</code> the positive branch stops at <code>⊢ some w = Heap.singleton l w l</code> and the negative one at <code>⊢ Heap.singleton l v x = Heap.singleton l w x</code>. The rule is mechanical — every defined name that appears in the goal has to appear in the brackets.",
      "variants": "Write at a <i>different</i> location and <code>write_singleton</code> becomes false: <code>Heap.write (Heap.singleton l v) l' w</code> is a two-cell heap, and no singleton. Likewise <code>Heap.erase (Heap.singleton l v) l'</code> for <code>l' ≠ l</code> is still <code>Heap.singleton l v</code>, not <code>Heap.empty</code> — the correct lemma there needs <code>l' ≠ l</code> and concludes with the singleton unchanged. Both failures are the same failure: these lemmas are true because the footprint of the operation and the footprint of the heap coincide exactly, and separation logic is the discipline of arranging for that to be the case."
    },
    {
      "t": "sec",
      "s": "The interface, assembled"
    },
    {
      "t": "p",
      "h": "Here is everything this chapter proved, in the form you will actually use it: as a rewrite set. From M2 onwards, a proof about heaps that mentions <code>if</code> is a proof that has gone below the interface, and almost always a proof that has gone wrong."
    },
    {
      "t": "tbl",
      "head": ["lemma", "statement", "what it is for"],
      "rows": [
        ["<code>singleton_same</code>", "<code>Heap.singleton l v l = some v</code>", "reading the one cell you own"],
        ["<code>singleton_other</code>", "<code>x ≠ l → Heap.singleton l v x = none</code>", "the singleton owns nothing else — this is exactness"],
        ["<code>write_same</code>", "<code>Heap.write h l v l = some v</code>", "read-after-write"],
        ["<code>write_other</code>", "<code>x ≠ l → Heap.write h l v x = h x</code>", "a write is invisible off its own cell — locality, in miniature"],
        ["<code>erase_same</code>", "<code>Heap.erase h l l = none</code>", "the cell is gone"],
        ["<code>erase_other</code>", "<code>x ≠ l → Heap.erase h l x = h x</code>", "a free is invisible off its own cell"],
        ["<code>write_shadow</code>", "<code>write (write h l v₁) l v₂ = write h l v₂</code>", "only the last write to a cell is observable"],
        ["<code>erase_write_same</code>", "<code>erase (write h l v) l = erase h l</code>", "a store into a cell about to be freed is dead"],
        ["<code>write_comm</code>", "<code>l₁ ≠ l₂ → write (write h l₁ v₁) l₂ v₂ = write (write h l₂ v₂) l₁ v₁</code>", "disjoint writes commute — the germ of the frame rule"],
        ["<code>write_singleton</code>", "<code>write (singleton l v) l w = singleton l w</code>", "the write rule, computed"],
        ["<code>erase_singleton</code>", "<code>erase (singleton l v) l = Heap.empty</code>", "the free rule, computed"]
      ],
      "cap": "The eleven equations. Exactly four carry a disequality, and those four are exactly the places where aliasing could have bitten."
    },
    {
      "t": "p",
      "h": "What is conspicuously missing is any way to put two heaps together. That is M2: <code>Heap.disjoint</code>, <code>Heap.union</code>, and the proof that <code>(Heap, union, empty)</code> is a partial commutative monoid. The proofs there have the same shape as the ones here — <code>funext</code> and a case split — but the case split is on <code>h₁ l</code> being <code>none</code> or <code>some v</code> rather than on a location equality, so <code>cases hl : h₁ l with …</code> replaces <code>by_cases</code>. Everything else carries over."
    },
    {
      "t": "dod",
      "h": "You have a heap API characterised by lookup equations, and you never need to unfold a heap operation again — only rewrite with these lemmas."
    }
  ]
});
