/* M8 — Locality and the frame rule
   Content for the Separation Logic workbook. See ../AUTHORING.md for the block schema. */

registerChapter({
  "id": "m8",
  "num": "M8",
  "phase": "Phase 2 · Program logic",
  "title": "Locality and the frame rule",
  "blurb": "The defining theorem of the subject — proved from the semantics, not assumed.",
  "orient": {
    "youWill": [
      "State the two side conditions the frame rule needs — <code>HeapLocal</code> for the heap, <code>Preserves</code> for the store — and say which failure each one rules out.",
      "Prove locality for every primitive command, including the two that change the heap, and for sequencing.",
      "Prove <code>hoare_frame</code> itself: eight lines, no axiom, no <code>sorry</code>.",
      "Exhibit a command and a state for which the naïve frame rule is <i>false</i>, and name the hypothesis that fails.",
      "Read past Lean’s structure projections with <code>show</code>, with <code>have h' : … = _ := h</code>, and with <code>rename_i</code>."
    ],
    "needs": [
      "M2’s heap algebra: <code>Heap.disjoint</code>, <code>Heap.union</code>, and the four rewriting lemmas <code>union_of_none</code>, <code>union_of_some</code>, <code>write_other</code>, <code>erase_other</code>.",
      "M4’s <code>∗</code> unfolded by hand — the six-component pattern <code>⟨h₁, h₂, hd, hu, hp, hq⟩</code>.",
      "M5’s <code>Exec</code> with its constructors and their side conditions, and M6’s <code>Hoare</code>.",
      "The tactics <code>intro</code>, <code>cases … with</code>, <code>refine</code>, <code>obtain</code>, <code>rcases</code>, <code>funext</code>, <code>by_cases</code>, <code>subst</code>. All were introduced in M0–M4."
    ],
    "payoff": "This is the chapter the rest of the workbook stands on: from M9 onward every verification is <code>hoare_seq</code> + <code>hoare_frame</code> + a small rule, and <code>Exec</code> never appears again."
  },
  "blocks": [
    {
      "t": "h3",
      "s": "The idea"
    },
    {
      "t": "txt",
      "src": "        { P }  c  { Q }\n    ─────────────────────────\n      { P ∗ R }  c  { Q ∗ R }"
    },
    {
      "t": "svg",
      "src": "\n<svg viewBox=\"0 0 560 186\" role=\"img\" aria-label=\"The frame rule\">\n  <g class=\"dg\">\n    <text x=\"12\" y=\"18\" class=\"dg-lab\">before</text>\n    <rect x=\"12\" y=\"28\" width=\"120\" height=\"38\" rx=\"7\" class=\"dg-box a\"/>\n    <text x=\"72\" y=\"52\" text-anchor=\"middle\" class=\"dg-t\">P</text>\n    <rect x=\"140\" y=\"28\" width=\"120\" height=\"38\" rx=\"7\" class=\"dg-box c\"/>\n    <text x=\"200\" y=\"52\" text-anchor=\"middle\" class=\"dg-t\">R</text>\n\n    <path class=\"dg-arr\" d=\"M282 48 L 330 48\"/>\n    <text x=\"306\" y=\"36\" text-anchor=\"middle\" class=\"dg-note\">c</text>\n\n    <text x=\"348\" y=\"18\" class=\"dg-lab\">after</text>\n    <rect x=\"348\" y=\"28\" width=\"120\" height=\"38\" rx=\"7\" class=\"dg-box b\"/>\n    <text x=\"408\" y=\"52\" text-anchor=\"middle\" class=\"dg-t\">Q</text>\n    <rect x=\"416\" y=\"28\" width=\"0\" height=\"0\"/>\n    <rect x=\"476\" y=\"28\" width=\"64\" height=\"38\" rx=\"7\" class=\"dg-box c\"/>\n    <text x=\"508\" y=\"52\" text-anchor=\"middle\" class=\"dg-t\">R</text>\n\n    <text x=\"12\" y=\"104\" class=\"dg-note\">c only touches the P-part. The R-part is untouched, byte for byte —</text>\n    <text x=\"12\" y=\"124\" class=\"dg-note\">so the same proof about c works inside any larger heap.</text>\n    <text x=\"12\" y=\"152\" class=\"dg-note\">The rule is not a convenience: it is a theorem about the semantics of c.</text>\n  </g>\n</svg>"
    },
    {
      "t": "p",
      "h": "“If <code>c</code> works correctly on the memory it owns, it also works correctly in the presence of extra, disjoint memory, and it leaves that extra memory alone.” Every textbook draws this box diagram. What almost none of them do is <b>prove it</b>, because in most presentations it is an axiom of the proof system."
    },
    {
      "t": "note",
      "h": "The frame rule is not a convenience and not a syntactic trick. It is a <b>theorem about the operational semantics</b>: it holds because our commands are local — they only touch the cells they can see. If you added a command that could observe the size of the whole heap, or allocate at a fixed address, the frame rule would become false. Proving it forces you to say precisely what “local” means.",
      "title": "The one thing to remember",
      "kind": "key"
    },
    {
      "t": "p",
      "h": "Taking it as an axiom is not merely inelegant. An axiom is a promise about every command you will ever add to the language, and it is a promise you can break by accident. Here you will discharge it instead, which means finding out exactly what the promise <i>says</i>."
    },
    {
      "t": "steps",
      "title": "The informal argument, and where each step needs a hypothesis",
      "items": [
        {
          "k": "Split",
          "h": "The precondition is <code>P ∗ R</code>, so the starting heap <code>h</code> comes with a decomposition <code>h = hP ∪ hR</code> with <code>hP</code> and <code>hR</code> disjoint. This is just unfolding <code>star</code>; no hypothesis needed."
        },
        {
          "k": "Run it small",
          "h": "Feed <code>hP</code> to the triple you already have. You get some final state <code>s'</code> with <code>Q</code> holding of its heap. Still no new hypothesis."
        },
        {
          "k": "Lift the run",
          "h": "You now need an execution starting from the <i>big</i> heap <code>hP ∪ hR</code>. Nothing in <code>Hoare P c Q</code> gives you one. <b>This is the first gap</b>, and <code>HeapLocal c</code> is exactly what fills it."
        },
        {
          "k": "Reassemble",
          "h": "To conclude <code>(Q ∗ R)</code> of the final heap you must produce a split of it. The natural cut is <code>s'.heap ∪ hR</code> — and you must prove those two are disjoint. <b>This is the second gap</b>, and it is why <code>HeapLocal</code> carries a disjointness conjunct."
        },
        {
          "k": "Re-establish R",
          "h": "The final <code>R</code> has to hold under the <i>new store</i>, and the command may have overwritten a variable <code>R</code> mentions. <b>This is the third gap</b>, and <code>Preserves c R</code> fills it."
        }
      ]
    },
    {
      "t": "p",
      "h": "Three gaps, two definitions: the first two are both about the heap, so they go into one predicate, and the third gets its own. What follows is those two definitions, then their proofs for each command, then the theorem."
    },
    {
      "t": "h3",
      "s": "Two obligations, not one"
    },
    {
      "t": "p",
      "h": "There are two independent ways the naïve rule can fail, and you need a condition for each."
    },
    {
      "t": "h4",
      "s": "1. Heap locality"
    },
    {
      "t": "p",
      "h": "Seven things are being said here, and every one of them is load-bearing. The callouts take them in order."
    },
    {
      "t": "anat",
      "src": "def HeapLocal (c : Cmd) : Prop :=\n  ∀ σ h hFrame s',\n    Heap.disjoint h hFrame →\n    Exec c ⟨σ, h⟩ s' →\n    Heap.disjoint s'.heap hFrame ∧\n    ∃ r : State,\n      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧\n      r.store = s'.store ∧\n      r.heap = Heap.union s'.heap hFrame",
      "parts": [
        {
          "m": "∀ σ h hFrame s'",
          "h": "A store, the command’s <i>own</i> heap, an arbitrary disjoint frame, and the state the small run ended in. Nothing here says <code>hFrame</code> is small or well-behaved: it is any heap at all, subject only to the disjointness below."
        },
        {
          "m": "Heap.disjoint h hFrame",
          "h": "The only assumption about the frame. On paper you would say “let <code>h ⊎ hFrame</code> be defined”; Lean has no partial <code>⊎</code>, so the definedness becomes a hypothesis you carry (this is the M2 move, and it recurs here)."
        },
        {
          "m": "Exec c ⟨σ, h⟩ s'",
          "h": "The small run — the one you already know about, because it came out of a <code>Hoare</code> triple. <code>⟨σ, h⟩</code> is the anonymous constructor for the <code>State</code> structure; Lean will print it back as <code>{ store := σ, heap := h }</code>."
        },
        {
          "m": "Heap.disjoint s'.heap hFrame",
          "h": "Conclusion 1: the command did not annex any of the frame’s territory. Needed to rebuild a <code>∗</code> in the postcondition. This conjunct is <i>not</i> in the usual textbook statement; see the correction below."
        },
        {
          "m": "∃ r : State",
          "h": "Conclusion 2 is existential rather than an equation because <code>Exec</code> is a relation, not a function. You must <i>exhibit</i> the big run’s final state. In practice you write it down explicitly — <code>⟨σ, Heap.union h hFrame⟩</code> and so on."
        },
        {
          "m": "r.store = s'.store",
          "h": "The frame does not change what the command does to the store."
        },
        {
          "m": "r.heap = Heap.union s'.heap hFrame",
          "h": "The heart of it. The big run’s heap is the small run’s heap with the frame glued back on, <i>unchanged</i>. Not “agrees on the frame’s domain” — literally equal as a function."
        }
      ]
    },
    {
      "t": "quote",
      "h": "Adding disjoint memory before execution does not change what the command does, and that memory is still there, unchanged, afterwards."
    },
    {
      "t": "p",
      "h": "Read the last two conjuncts as a commuting square: “extend by <code>hFrame</code>, then run” equals “run, then extend by <code>hFrame</code>”. That is a simulation statement about the operational semantics, and it is provable or not depending entirely on which commands the language has. It is <i>not</i> a property of the assertion language."
    },
    {
      "t": "note",
      "h": "The syllabus states <code>HeapLocal</code> without the conjunct <code>Heap.disjoint s'.heap hFrame</code>. Add it. Without it the frame theorem is unprovable: to rebuild <code>Q ∗ R</code> in the postcondition you must supply a disjointness proof for the <i>final</i> heap and the frame, and nothing else in the statement gives it to you. It is true for every command in our language (write preserves the domain, free shrinks it, the rest do not touch the heap), so it costs nothing to include.",
      "title": "A correction to the statement",
      "kind": "warn"
    },
    {
      "t": "detail",
      "title": "What the proof looks like without the disjointness conjunct",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "It is worth seeing the gap rather than being told about it. Here is <code>HeapLocal</code> as the syllabus states it, and the frame proof carried as far as it will go:"
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "-- the syllabus version: no `Heap.disjoint s'.heap hFrame` conjunct\ndef HeapLocalWeak (c : Cmd) : Prop :=\n  ∀ σ h hFrame s',\n    Heap.disjoint h hFrame →\n    Exec c ⟨σ, h⟩ s' →\n    ∃ r : State,\n      Exec c ⟨σ, Heap.union h hFrame⟩ r ∧\n      r.store = s'.store ∧\n      r.heap = Heap.union s'.heap hFrame\n\nexample {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocalWeak c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R) := by\n  intro σ h hstar\n  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar\n  obtain ⟨s', hex, hq⟩ := hc σ hP hp\n  obtain ⟨r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex\n  subst hu\n  refine ⟨r, hrex, s'.heap, hR, ?_, hrhp, ?_, ?_⟩\n  · sorry                       -- ⊢ s'.heap.disjoint hR  — nothing proves this\n  · rw [hrst]; exact hq\n  · exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",
          "cap": "compiles (with one sorry) against prelude/m8.lean"
        },
        {
          "t": "p",
          "h": "The first <code>?_</code> is where you are stranded. Lean prints:"
        },
        {
          "t": "state",
          "src": "case refine_1\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocalWeak c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ s'.heap.disjoint hR",
          "cap": "the goal at the sorry"
        },
        {
          "t": "p",
          "h": "Look at what is in scope. <code>hd</code> is about <code>hP</code>, the heap <i>before</i> the command; <code>hrhp</code> tells you what <code>r.heap</code> is but says nothing about <code>s'.heap</code> versus <code>hR</code>. There is genuinely no route. The information has to come from the locality assumption, so it goes into the locality assumption."
        }
      ]
    },
    {
      "t": "h4",
      "s": "2. Store stability"
    },
    {
      "t": "p",
      "h": "A framed assertion may mention program variables, and a command may change them. The classic counterexample:"
    },
    {
      "t": "txt",
      "src": "  valid:    { x = 0 }  x := 1  { x = 1 }\n  framing \"x = 0\" gives\n  invalid:  { x = 0 ∗ x = 0 }  x := 1  { x = 1 ∗ x = 0 }     ← false"
    },
    {
      "t": "p",
      "h": "Nothing about heaps went wrong here; the frame simply talked about a variable the command overwrote. So we need a second, semantic side condition:"
    },
    {
      "t": "code",
      "src": "def Preserves (c : Cmd) (R : Assertion) : Prop :=\n  ∀ s s', Exec c s s' → ∀ hFrame, R s.store hFrame → R s'.store hFrame"
    },
    {
      "t": "p",
      "h": "Note what <code>Preserves</code> quantifies over. It fixes the <i>heap</i> <code>hFrame</code> and lets only the store move: <code>R s.store hFrame → R s'.store hFrame</code>. That is the right shape, because the frame’s heap is untouched by hypothesis (that is <code>HeapLocal</code>’s job) and the only thing that can go wrong is the store."
    },
    {
      "t": "cmp",
      "left": {
        "t": "The syntactic side condition you will find in textbooks",
        "kind": "bad",
        "h": "<code>modifies(c) ∩ freeVars(R) = ∅</code>. To state it you need a syntactic <code>modifies</code> function on commands, a <code>freeVars</code> function on assertions — and assertions here are <i>arbitrary Lean predicates</i> <code>Store → Heap → Prop</code>, which have no syntax to take the free variables of. It is unstatable in this development."
      },
      "right": {
        "t": "The semantic side condition we use",
        "kind": "good",
        "h": "<code>Preserves c R</code> says the same thing where it matters and is strictly weaker: it also accepts <code>R</code>s that mention a variable the command writes, as long as the write does not disturb them. And every instance we need is discharged by one of two one-line helpers."
      }
    },
    {
      "t": "detail",
      "title": "The counterexample, in Lean",
      "tag": "aside",
      "open": false,
      "blocks": [
        {
          "t": "p",
          "h": "The <code>x := 1</code> example above is not folklore; it is a theorem. Both halves are proved here: the small triple holds, and the framed triple is refutable."
        },
        {
          "t": "code",
          "tag": "illustration",
          "src": "theorem frame_without_preserves_is_false (x : Var) :\n    Hoare (pure (fun σ => σ x = 0)) (.assign x (.const 1)) (pure (fun σ => σ x = 1))\n    ∧ ¬ Hoare (pure (fun σ => σ x = 0) ∗ fact (fun σ => σ x = 0))\n              (.assign x (.const 1))\n              (pure (fun σ => σ x = 1) ∗ fact (fun σ => σ x = 0)) := by\n  constructor\n  · intro σ h hp\n    obtain ⟨hx, he⟩ := hp\n    refine ⟨⟨Store.set σ x 1, h⟩, Exec.assign, ?_, he⟩\n    show Store.set σ x 1 x = 1\n    simp [Store.set]\n  · intro hcontra\n    obtain ⟨s', hex, hq⟩ :=\n      hcontra (fun _ => 0) Heap.empty\n        ⟨Heap.empty, Heap.empty, disjoint_empty_left _,\n         (union_empty_left _).symm, ⟨rfl, rfl⟩, rfl⟩\n    cases hex\n    obtain ⟨h₁, h₂, hd, hu, hq1, hr1⟩ := hq\n    have hbad : Store.set (fun _ => 0) x 1 x = 0 := hr1\n    simp [Store.set] at hbad",
          "cap": "compiles against prelude/m8.lean"
        },
        {
          "t": "p",
          "h": "The witness is the smallest possible: store <code>fun _ => 0</code>, heap <code>Heap.empty</code>, cut into <code>Heap.empty ∗ Heap.empty</code>. After <code>cases hex</code> the final store is <code>Store.set (fun _ => 0) x 1</code>, and the framed <code>R</code> demands that its value at <code>x</code> be <code>0</code>. Note that the heap never enters the argument at all — which is the point: this failure has nothing to do with separation."
        },
        {
          "t": "p",
          "h": "Three details of the Lean, since none of them is guessable. <b>The pairs.</b> <code>pure φ</code> is <code>aAnd (fact φ) emp</code>, so a proof of it is a pair, and <code>obtain ⟨hx, he⟩ := hp</code> splits it into <code>hx : fact (fun σ => σ x = 0) σ h</code> and <code>he : emp σ h</code>. The <code>⟨rfl, rfl⟩</code> inside the big anonymous constructor builds one back the other way — <code>rfl</code> for <code>(fun _ => 0) x = 0</code> and <code>rfl</code> for <code>Heap.empty = Heap.empty</code>. <b>The frame is <code>fact</code>, not <code>pure</code>.</b> <code>fact</code> ignores the heap entirely, so the framed assertion imposes nothing spatial and the refutation cannot be blamed on a bad heap split. <b>The <code>show</code>.</b> After the <code>refine</code> the goal is:"
        },
        {
          "t": "state",
          "src": "x : Var\nσ : Store\nh : Heap\nhx : fact (fun σ => σ x = 0) σ h\nhe : emp σ h\n⊢ fact (fun σ => σ x = 1) { store := σ.set x 1, heap := h }.store { store := σ.set x 1, heap := h }.heap",
          "cap": "the remaining ?_ in the first half"
        },
        {
          "t": "p",
          "h": "<code>show Store.set σ x 1 x = 1</code> restates that as the arithmetic fact it is — unfolding <code>fact</code>, the projection and the application in one definitional step — and <code>simp [Store.set]</code> reduces <code>if x = x then 1 else σ x</code> to <code>1</code>. One display quirk to expect here: the goal one line earlier prints our assertion as <code>_root_.pure</code>, because <code>Pure.pure</code> from the standard library also lives under that name and Lean disambiguates."
        }
      ]
    },
    {
      "t": "p",
      "h": "For heap-only assertions such as <code>l ↦ v</code> this is free. Two helpers make it free in practice:"
    },
    {
      "t": "code",
      "src": "def HeapOnly (R : Assertion) : Prop := ∀ σ σ' h, R σ h → R σ' h\n\ntheorem preserves_of_heapOnly {R : Assertion} (c : Cmd) (h : HeapOnly R) : Preserves c R :=\n  fun s s' _ hFrame hr => h s.store s'.store hFrame hr\n\ntheorem heapOnly_pointsTo (l : Loc) (v : Val) : HeapOnly (l ↦ v) :=\n  fun _ _ _ hr => hr\n\ntheorem heapOnly_emp : HeapOnly emp := fun _ _ _ hr => hr\n\ntheorem heapOnly_star {P Q : Assertion} (hp : HeapOnly P) (hq : HeapOnly Q) :\n    HeapOnly (P ∗ Q) := by\n  intro σ σ' h ⟨h₁, h₂, hd, hu, h1, h2⟩\n  exact ⟨h₁, h₂, hd, hu, hp σ σ' h₁ h1, hq σ σ' h₂ h2⟩"
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>HeapOnly R</code>",
          "h": "The store argument is ignored: <code>R σ h → R σ' h</code> for <i>any</i> two stores. True of <code>emp</code>, of <code>l ↦ v</code>, and of any <code>∗</code> of such things. Not available for <code>fact φ</code> or <code>pure φ</code>: <code>HeapOnly (fact φ)</code> unfolds to <code>∀ σ σ', φ σ → φ σ'</code>, which says <code>φ</code> is constant. For a <code>φ</code> that actually reads a variable it is false, and that is precisely the case you care about — so treat these two as out of reach and use the other route below."
        },
        {
          "k": "<code>preserves_of_heapOnly</code>",
          "h": "The bridge. Note the argument order: <code>(c : Cmd)</code> comes <i>first and explicitly</i>, so at a use site you will almost always write <code>preserves_of_heapOnly _ (…)</code> and let unification recover <code>c</code>."
        },
        {
          "k": "<code>heapOnly_pointsTo</code>, <code>heapOnly_emp</code>",
          "h": "Both are <code>fun _ _ _ hr => hr</code> — the assertion literally does not look at its store argument, so the implication is the identity. This is the payoff for having defined <code>pointsTo</code> as <code>fun _ h => h = Heap.singleton l v</code> with an ignored first argument back in M3."
        },
        {
          "k": "<code>heapOnly_star</code>",
          "h": "Closure under <code>∗</code>. The proof destructures the star with the same six-component pattern you have used since M4 and rebuilds it with the two halves pushed through. Nothing about the heaps changes; only the store is swapped."
        }
      ]
    },
    {
      "t": "note",
      "kind": "tip",
      "title": "How you will actually discharge Preserves",
      "h": "Two routes, and you pick by looking at the framed assertion. If <code>R</code> is spatial (built from <code>↦</code>, <code>emp</code> and <code>∗</code>), use <code>preserves_of_heapOnly</code>. If <code>R</code> is anything at all but the command is <code>write</code> or <code>free</code>, M9 gives you <code>preserves_of_storeStable</code>, which observes that those two commands do not touch the store and therefore preserve <i>every</i> assertion. Between them they cover every obligation in this workbook except one, and that one — a pure fact about <code>tmp₁</code> surviving a load into <code>tmp₂</code> — is M9’s <code>preserves_load_fact</code>."
    },
    {
      "t": "h3",
      "s": "Reading Lean’s output in this chapter"
    },
    {
      "t": "p",
      "h": "The goal states below are long, and they are long for a reason worth understanding before you start: <code>Exec</code>’s constructors are stated about a state <code>s</code> and refer to <code>s.heap</code>, but you always apply them to a state you built yourself as <code>⟨σ, h⟩</code>. Lean does not simplify <code>{ store := σ, heap := h }.heap</code> to <code>h</code> in the display, even though the two are definitionally equal. So every goal in this chapter is a small heap expression wearing a large hat."
    },
    {
      "t": "dl",
      "items": [
        {
          "k": "<code>h.disjoint hFrame</code>",
          "h": "This is <code>Heap.disjoint h hFrame</code>. Lean prints a function whose first explicit argument’s type matches its namespace using dot notation. Same for <code>h.union hFrame</code>, <code>h.write l v</code>, <code>h.erase l</code>, <code>σ.set x v</code>. Your source may say <code>Heap.union h hFrame</code>; the goal will say <code>h.union hFrame</code>. They are the same term."
        },
        {
          "k": "<code>{ store := σ, heap := h }.heap</code>",
          "h": "The heap field of a state you constructed. Definitionally <code>h</code>, but <i>syntactically</i> not <code>h</code>, and <code>rw</code> matches syntactically. Whenever a rewrite fails with “did not find an occurrence”, check whether this is why."
        },
        {
          "k": "<code>old✝</code>, <code>v✝</code>, <code>s'✝</code>",
          "h": "Inaccessible names. <code>cases</code> introduced them because the constructor binds them implicitly and you did not name them. You cannot type a <code>✝</code>, so you cannot refer to these directly — you either write <code>_</code> and let unification fill them, or you rename with <code>rename_i</code>."
        },
        {
          "k": "<code>case pos</code> / <code>case neg</code>",
          "h": "The two branches of <code>by_cases h : p</code>: <code>pos</code> has <code>h : p</code>, <code>neg</code> has <code>h : ¬p</code>. Note that <code>neg</code> prints as <code>hxl : ¬x = l</code>, not <code>x ≠ l</code> — the two are the same, and lemmas stated with <code>≠</code> accept it."
        },
        {
          "k": "<code>case refine_1</code>",
          "h": "The <code>n</code>-th <code>?_</code> hole left by a <code>refine</code>, numbered in order of appearance."
        }
      ]
    },
    {
      "t": "note",
      "kind": "info",
      "title": "A tactic you have not seen yet",
      "h": "<code>rename_i</code> gives names to inaccessible hypotheses, counting <i>from the right</i>: <code>rename_i sMid</code> names the last one, <code>rename_i a b</code> names the last two. Accessible hypotheses are skipped, so it lands on the <code>✝</code> names regardless of what sits between them. It appears once in the solutions, in <code>heapLocal_seq</code>, where <code>cases</code> on a sequential execution introduces the intermediate state without a name and you cannot proceed without one."
    },
    {
      "t": "sec",
      "s": "Exercises · locality of each command"
    },
    {
      "t": "ex",
      "id": "m8-1",
      "name": "heapLocal_skip / heapLocal_assign / heapLocal_load",
      "hard": false,
      "why": "The three commands that do not modify the heap. Locality is nearly definitional — but the load still has to show that its side condition survives the extension. Do these first for a second reason: they are where you learn to read the five-component anonymous constructor that every remaining proof in the chapter reuses.",
      "setup": "In scope: <code>HeapLocal</code>, all of <code>Exec</code>’s constructors, and the M2 lemma <code>union_of_some : h₁ l = some v → Heap.union h₁ h₂ l = some v</code>. Note that <code>union_of_some</code> takes <code>h₂</code> explicitly and <code>h₁</code>, <code>l</code>, <code>v</code> implicitly, so the call is <code>union_of_some hFrame hl</code>.",
      "goal": "theorem heapLocal_skip : HeapLocal .skip\ntheorem heapLocal_assign (x : Var) (e : Atom) : HeapLocal (.assign x e)\ntheorem heapLocal_load (x : Var) (l : Loc) : HeapLocal (.load x l)",
      "hints": [
        "All three have the same skeleton. <code>intro</code> the six binders of <code>HeapLocal</code>, then <code>cases hex</code> — the command’s own semantics tells you what <code>s'</code> actually is, and once you know that, the goal tells you which <code>r</code> to supply.",
        "After <code>cases</code> the goal is <code>… ∧ ∃ r, … ∧ … ∧ …</code>. One anonymous constructor covers all of it: <code>⟨disjointness, the state r, the Exec proof, rfl, rfl⟩</code>. Since none of these commands touches the heap, the disjointness proof is <code>hd</code> itself and both equations are <code>rfl</code>.",
        "The state to supply is “what the command did, but starting from <code>Heap.union h hFrame</code>”. For <code>skip</code> that is <code>⟨σ, Heap.union h hFrame⟩</code>; for <code>assign</code>, <code>⟨Store.set σ x (e.eval σ), Heap.union h hFrame⟩</code>.",
        "For <code>load</code> the <code>Exec</code> proof is not free: <code>Exec.load</code> needs <code>(h ∪ hFrame) l = some v</code> and you have <code>h l = some v</code>. Use <code>refine … Exec.load ?_ …</code> and close the hole with <code>union_of_some hFrame hl</code>. The value read is inaccessible (<code>v✝</code>), so write <code>Store.set σ x _</code> and let unification fill the blank."
      ],
      "sol": "theorem heapLocal_skip : HeapLocal .skip := by\n  intro σ h hFrame s' hd hex\n  cases hex\n  exact ⟨hd, ⟨σ, Heap.union h hFrame⟩, Exec.skip, rfl, rfl⟩\n\ntheorem heapLocal_assign (x : Var) (e : Atom) : HeapLocal (.assign x e) := by\n  intro σ h hFrame s' hd hex\n  cases hex\n  exact ⟨hd, ⟨Store.set σ x (e.eval σ), Heap.union h hFrame⟩, Exec.assign, rfl, rfl⟩\n\ntheorem heapLocal_load (x : Var) (l : Loc) : HeapLocal (.load x l) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | load hl =>\n      refine ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩, Exec.load ?_, rfl, rfl⟩\n      exact union_of_some hFrame hl",
      "expl": "<code>union_of_some</code> is the load case in one lemma: if the small heap already has the cell, the left-biased union has it too, with the same value. Notice the frame cannot change what a load reads — that is <i>exactly</i> the locality property, and it is why the small-footprint load rule scales.",
      "walk": [
        {
          "tac": "intro σ h hFrame s' hd hex",
          "h": "<code>HeapLocal .skip</code> is a <code>∀</code> under the hood, so <code>intro</code> peels off all six binders at once: the store, the small heap, the frame, the small run’s result, the disjointness hypothesis, and the execution."
        },
        {
          "tac": "cases hex",
          "h": "There is exactly one constructor that can produce <code>Exec .skip ⟨σ, h⟩ s'</code>, namely <code>Exec.skip</code>, and it forces <code>s' = ⟨σ, h⟩</code>. So <code>cases</code> eliminates <code>s'</code> entirely and rewrites the goal in terms of <code>⟨σ, h⟩</code>. The branch is labelled <code>case skip</code>."
        },
        {
          "tac": "exact ⟨hd, ⟨σ, Heap.union h hFrame⟩, Exec.skip, rfl, rfl⟩",
          "h": "Five components for <code>A ∧ ∃ r, B ∧ C ∧ D</code>. Anonymous constructors nest to the right automatically, so this is <code>⟨hd, ⟨⟨σ, …⟩, ⟨Exec.skip, ⟨rfl, rfl⟩⟩⟩⟩</code> written flat. <code>hd</code> proves the first conjunct because <code>skip</code> left the heap alone; the two <code>rfl</code>s work because the state you supplied is literally the right one."
        },
        {
          "tac": "theorem heapLocal_assign (x : Var) (e : Atom) : HeapLocal (.assign x e) := by",
          "h": "Second theorem, same shape. <code>x</code> and <code>e</code> are parameters of the command, not of the locality property."
        },
        {
          "tac": "intro σ h hFrame s' hd hex",
          "h": "Identical to before."
        },
        {
          "tac": "cases hex",
          "h": "<code>Exec.assign</code> is the only constructor, and it fixes <code>s' = ⟨Store.set σ x (e.eval σ), h⟩</code>. Note that the evaluation happens in the <i>initial</i> store, which is why the frame cannot affect it."
        },
        {
          "tac": "exact ⟨hd, ⟨Store.set σ x (e.eval σ), Heap.union h hFrame⟩, Exec.assign, rfl, rfl⟩",
          "h": "Same five components. The witness state is the assignment’s effect applied to the big heap: same store update, bigger heap. <code>rfl</code> closes <code>r.store = s'.store</code> because both sides are <code>Store.set σ x (e.eval σ)</code> on the nose."
        },
        {
          "tac": "theorem heapLocal_load (x : Var) (l : Loc) : HeapLocal (.load x l) := by",
          "h": "Third theorem. This is the one with content."
        },
        {
          "tac": "intro σ h hFrame s' hd hex",
          "h": "As before."
        },
        {
          "tac": "cases hex with",
          "h": "Here you need the named form, because <code>Exec.load</code> carries a side condition you want to keep."
        },
        {
          "tac": "| load hl =>",
          "h": "Names that side condition <code>hl : { store := σ, heap := h }.heap l = some v✝</code>. The value <code>v✝</code> stays inaccessible — you never named it, and you do not need to."
        },
        {
          "tac": "refine ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩, Exec.load ?_, rfl, rfl⟩",
          "h": "<code>refine</code> rather than <code>exact</code> because one component is not yet available. The <code>_</code> in <code>Store.set σ x _</code> is a hole Lean fills by unification (it becomes <code>v✝</code>); the <code>?_</code> in <code>Exec.load ?_</code> is a hole <i>you</i> promise to fill, and it becomes the next goal."
        },
        {
          "tac": "exact union_of_some hFrame hl",
          "h": "The remaining goal is <code>{ store := σ, heap := h.union hFrame }.heap l = some v✝</code> — up to the projection, exactly <code>union_of_some</code>’s conclusion. This one line is the whole mathematical content of the load case: <b>the frame cannot change what a load reads</b>, because the union is left-biased and the small heap already owns the cell."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "heapLocal_skip, tactic by tactic",
          "start": "⊢ HeapLocal Cmd.skip",
          "steps": [
            {
              "tac": "intro σ h hFrame s' hd hex",
              "state": "σ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nhex : Exec Cmd.skip { store := σ, heap := h } s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec Cmd.skip { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Everything is now hypotheses and one goal. Read the goal: a conjunction whose second half is an existential over states. That shape is what the five-component <code>⟨…⟩</code> matches."
            },
            {
              "tac": "cases hex",
              "state": "case skip\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\n⊢ { store := σ, heap := h }.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec Cmd.skip { store := σ, heap := h.union hFrame } r ∧\n        r.store = { store := σ, heap := h }.store ∧ r.heap = { store := σ, heap := h }.heap.union hFrame",
              "h": "Two things changed. <code>s'</code> and <code>hex</code> are gone — <code>cases</code> learned that <code>s'</code> had to be <code>⟨σ, h⟩</code> and substituted it. And the goal now shows the projections <code>{ store := σ, heap := h }.heap</code> rather than plain <code>h</code>. That is cosmetically ugly and mathematically irrelevant: <code>exact</code> checks up to definitional equality, so <code>hd : h.disjoint hFrame</code> closes the first conjunct without complaint."
            },
            {
              "tac": "exact ⟨hd, ⟨σ, Heap.union h hFrame⟩, Exec.skip, rfl, rfl⟩",
              "state": "No goals.",
              "h": "The witness is “the same state, but with the frame attached”."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "trace",
          "title": "heapLocal_load, tactic by tactic",
          "start": "x : Var\nl : Loc\n⊢ HeapLocal (Cmd.load x l)",
          "steps": [
            {
              "tac": "intro σ h hFrame s' hd hex",
              "state": "x : Var\nl : Loc\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nhex : Exec (Cmd.load x l) { store := σ, heap := h } s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec (Cmd.load x l) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "The same six binders as for <code>skip</code>, now with the command’s parameters <code>x</code> and <code>l</code> also in scope."
            },
            {
              "tac": "cases hex with | load hl =>",
              "state": "case load\nx : Var\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\n⊢ { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec (Cmd.load x l) { store := σ, heap := h.union hFrame } r ∧\n        r.store = { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.store ∧\n          r.heap =\n            { store := { store := σ, heap := h }.store.set x v✝, heap := { store := σ, heap := h }.heap }.heap.union\n              hFrame",
              "h": "<code>Exec.load</code> was the only applicable constructor. It brought two things: an inaccessible value <code>v✝</code>, and the side condition <code>hl</code>. Notice that <code>hl</code> is stated about <code>{ store := σ, heap := h }.heap l</code>, not about <code>h l</code>. That does not matter <i>here</i> because we only pass <code>hl</code> to a lemma (which checks up to defeq) — but it will matter in the next exercise, where we want to <code>rw</code> with it."
            },
            {
              "tac": "refine ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩, Exec.load ?_, rfl, rfl⟩",
              "state": "case load\nx : Var\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\n⊢ { store := σ, heap := h.union hFrame }.heap l = some v✝",
              "h": "One goal left: the side condition of the big run’s load. This is the moment of truth for the whole chapter — if reading from the extended heap could give a different answer, separation logic would not work."
            },
            {
              "tac": "exact union_of_some hFrame hl",
              "state": "No goals.",
              "h": "<code>union_of_some</code> has conclusion <code>Heap.union h₁ h₂ l = some v</code>; the goal is that with a <code>State.heap</code> projection wrapped around the left-hand side. <code>exact</code> sees through it."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "You can also do the load case with a single <code>exact</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "The <code>refine … ?_</code> in the corpus is a matter of taste; supplying the side condition inline works too:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "theorem heapLocal_load_alt (x : Var) (l : Loc) : HeapLocal (.load x l) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | load hl =>\n      exact ⟨hd, ⟨Store.set σ x _, Heap.union h hFrame⟩,\n             Exec.load (union_of_some hFrame hl), rfl, rfl⟩",
              "cap": "compiles against prelude/m8.lean"
            },
            {
              "t": "p",
              "h": "The reason to prefer the <code>refine</code> version when you are learning is that it puts the interesting obligation on the screen as its own goal, with a name and a type, instead of burying it inside a term."
            }
          ]
        }
      ],
      "pitfall": "You will try to name the value that was read: <code>cases hex with | load hl v</code>. Lean answers <code>Too many variable names provided at alternative `load`: 2 provided, but 1 expected</code>. <code>Exec.load</code>’s only <i>explicit</i> field is the side condition <code>hl</code>; the value <code>v</code> is implicit, and the <code>with | ctor a b</code> syntax names explicit fields only. If you really want the name, add <code>rename_i v</code> after the <code>cases</code> and then <code>Store.set σ x v</code> works. Usually you do not want it: <code>Store.set σ x _</code> lets unification supply it, and the proof is shorter.",
      "variants": "Drop the hypothesis <code>Heap.disjoint h hFrame</code> from <code>HeapLocal</code> and all three of these become <i>unprovable</i>, for a stupid-sounding but instructive reason: the first conclusion is <code>Heap.disjoint s'.heap hFrame</code>, which for these three commands <i>is</i> <code>Heap.disjoint h hFrame</code>, and you would have nothing to prove it with. Replace <code>Heap.union h hFrame</code> by <code>Heap.union hFrame h</code> throughout and the statement stays true but the load proof breaks: <code>union_of_some hFrame hl</code> no longer applies, because the left-biased union would consult the frame first. You would have to route through <code>union_comm hd</code> — that is, you would have to consume the disjointness hypothesis to recover the same fact. Left-biasedness is what makes the load case free."
    },
    {
      "t": "ex",
      "id": "m8-2",
      "name": "heapLocal_write",
      "hard": true,
      "why": "The first case with real content: you must show that writing into the union equals writing into the small heap and then re-uniting. It is also where you meet the two Lean manoeuvres that recur for the rest of the chapter — restating a hypothesis to get rid of a projection, and using <code>show</code> to state the goal in the form your lemmas are about.",
      "setup": "In scope from M1/M2: <code>write_same : Heap.write h l v l = some v</code>, <code>write_other : x ≠ l → Heap.write h l v x = h x</code>, <code>union_of_none</code>, <code>union_of_some</code>. Recall <code>Heap.disjoint h₁ h₂</code> unfolds to <code>∀ l, h₁ l = none ∨ h₂ l = none</code>, so proving one starts with <code>intro x</code> and using one is <code>hd x</code>.",
      "goal": "theorem heapLocal_write (l : Loc) (e : Atom) : HeapLocal (.write l e)",
      "hints": [
        "There are two obligations. (a) Disjointness is preserved, because <code>write</code> does not change the domain. (b) The heap equation <code>write (h ∪ hFrame) l v = (write h l v) ∪ hFrame</code>, which is a <code>funext</code> plus a split on <code>x = l</code>. Do (a) as a standalone <code>have</code> before touching the main goal.",
        "For (a): <code>intro x</code>, then <code>rcases hd x with hx | hx</code>. The right disjunct (<code>hFrame x = none</code>) transfers unchanged. The left disjunct (<code>h x = none</code>) needs a case split on <code>x = l</code>: if <code>x ≠ l</code> then <code>write_other</code> says nothing changed; if <code>x = l</code> you have both <code>h l = none</code> and <code>h l = some old</code>, which is a contradiction.",
        "The hypothesis <code>hl</code> that <code>cases</code> gave you is about <code>{ store := σ, heap := h }.heap l</code>, and <code>rw</code> will refuse to use it against a goal mentioning <code>h l</code>. Restate it: <code>have hl' : h l = _ := hl</code>. The <code>_</code> means “whatever the right-hand side was”; Lean elaborates <code>hl</code> against the stated shape and the projection evaporates.",
        "After the <code>refine</code>, the last goal is the heap equation wrapped in <code>State.heap</code> projections, so <code>funext</code> would work but every subsequent <code>rw</code> would fail. Put the goal in the shape you want first, with <code>show Heap.write (Heap.union h hFrame) l (e.eval σ) = Heap.union (Heap.write h l (e.eval σ)) hFrame</code>, and only then <code>funext x</code>.",
        "In the <code>x ≠ l</code> branch both sides reduce to a union, but you do not know whether <code>h x</code> is <code>none</code> or <code>some</code>. <code>cases hx : h x with | none => … | some w => …</code> splits it <i>and</i> records the equation as <code>hx</code>, which is what <code>union_of_none</code> / <code>union_of_some</code> need. Chain <code>hwx</code> and <code>hx</code> with <code>hwx.trans hx</code>."
      ],
      "sol": "theorem heapLocal_write (l : Loc) (e : Atom) : HeapLocal (.write l e) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | write hl =>\n      have hl' : h l = _ := hl\n      have hdw : Heap.disjoint (Heap.write h l (e.eval σ)) hFrame := by\n        intro x\n        rcases hd x with hx | hx\n        · by_cases hxl : x = l\n          · subst hxl; rw [hl'] at hx; exact absurd hx (by simp)\n          · left; rw [write_other h l x (e.eval σ) hxl]; exact hx\n        · exact Or.inr hx\n      refine ⟨hdw, ⟨σ, Heap.write (Heap.union h hFrame) l (e.eval σ)⟩,\n              Exec.write (union_of_some hFrame hl'), rfl, ?_⟩\n      show Heap.write (Heap.union h hFrame) l (e.eval σ)\n             = Heap.union (Heap.write h l (e.eval σ)) hFrame\n      funext x\n      by_cases hxl : x = l\n      · subst hxl\n        rw [write_same (Heap.union h hFrame) x (e.eval σ),\n            union_of_some hFrame (write_same h x (e.eval σ))]\n      · rw [write_other (Heap.union h hFrame) l x (e.eval σ) hxl]\n        have hwx : Heap.write h l (e.eval σ) x = h x := write_other h l x (e.eval σ) hxl\n        cases hx : h x with\n        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]\n        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]",
      "expl": "Read the disjointness argument carefully: at <code>x = l</code> we know <code>h l = some old</code>, so the disjointness hypothesis must have chosen the <i>right</i> disjunct, i.e. <code>hFrame l = none</code>; hence writing at <code>l</code> cannot collide. Everywhere else <code>write_other</code> says nothing changed. The heap equation then splits into “at <code>l</code>, both sides are <code>some (e.eval σ)</code>” and “elsewhere, both sides are <code>h x</code>-or-<code>hFrame x</code>”. The little <code>have hl' : h l = _ := hl</code> at the top is a Lean nicety: <code>hl</code> is stated about <code>⟨σ, h⟩.heap</code>, and <code>rw</code> will not see through the projection, so you restate it.",
      "walk": [
        {
          "tac": "intro σ h hFrame s' hd hex",
          "h": "The six binders of <code>HeapLocal</code>, as before."
        },
        {
          "tac": "cases hex with",
          "h": "Named form, because <code>Exec.write</code>’s side condition is needed twice."
        },
        {
          "tac": "| write hl =>",
          "h": "Binds <code>hl : { store := σ, heap := h }.heap l = some old✝</code> and fixes <code>s' = ⟨σ, Heap.write h l (e.eval σ)⟩</code>. The goal explodes into projections; ignore that for now."
        },
        {
          "tac": "have hl' : h l = _ := hl",
          "h": "The projection-stripping idiom. You assert a new hypothesis whose type you write yourself, with <code>_</code> for the part you do not want to spell out, and prove it by <code>hl</code> — which typechecks because the two types are definitionally equal. Now <code>hl' : h l = some old✝</code>, in a form <code>rw</code> can match."
        },
        {
          "tac": "have hdw : Heap.disjoint (Heap.write h l (e.eval σ)) hFrame := by",
          "h": "Obligation (a), proved separately so the main line stays readable. Stating it explicitly also pins down which heap you mean, saving you from the projections."
        },
        {
          "tac": "intro x",
          "h": "<code>Heap.disjoint</code> is a <code>∀ l, … ∨ …</code>, so a proof begins by fixing a location."
        },
        {
          "tac": "rcases hd x with hx | hx",
          "h": "Uses the assumption at <code>x</code> and splits the disjunction into two goals, naming the hypothesis <code>hx</code> in each. First branch: <code>hx : h x = none</code>. Second: <code>hx : hFrame x = none</code>."
        },
        {
          "tac": "· by_cases hxl : x = l",
          "h": "In the first branch the answer depends on whether <code>x</code> is the cell being written. Splits into <code>case pos</code> (<code>hxl : x = l</code>) and <code>case neg</code> (<code>hxl : ¬x = l</code>)."
        },
        {
          "tac": "· subst hxl; rw [hl'] at hx; exact absurd hx (by simp)",
          "h": "The contradiction branch. <code>subst hxl</code> eliminates one of the two variables. Which one is Lean’s choice, not yours: given <code>hxl : x = l</code> it is <code>l</code> that disappears, and every hypothesis is rewritten in terms of <code>x</code> — so <code>hl'</code> becomes <code>h x = some old✝</code>. (The trace below shows the state just <i>before</i> this <code>subst</code>, where both names are still present; the later <code>subst</code> in the <code>funext</code> branch is traced after it fires, and there you can see <code>l</code> gone from the whole context.) Then <code>rw [hl'] at hx</code> turns <code>hx : h x = none</code> into <code>hx : some old✝ = none</code>, and <code>absurd hx (by simp)</code> kills it — <code>absurd</code> takes a proof of <code>a</code> and a proof of <code>¬a</code> and returns anything, and <code>simp</code> supplies the <code>¬a</code> because it knows <code>some a ≠ none</code>."
        },
        {
          "tac": "· left; rw [write_other h l x (e.eval σ) hxl]; exact hx",
          "h": "The easy branch. <code>left</code> chooses the first disjunct of the goal <code>… = none ∨ hFrame x = none</code>. <code>write_other</code> (whose last argument is exactly <code>hxl : x ≠ l</code>) rewrites <code>Heap.write h l v x</code> to <code>h x</code>, and <code>hx</code> finishes."
        },
        {
          "tac": "· exact Or.inr hx",
          "h": "Second <code>rcases</code> branch: the frame is empty at <code>x</code>, which is already the right disjunct, whatever we did to <code>h</code>."
        },
        {
          "tac": "refine ⟨hdw, ⟨σ, Heap.write (Heap.union h hFrame) l (e.eval σ)⟩,\n        Exec.write (union_of_some hFrame hl'), rfl, ?_⟩",
          "h": "The five components again. Disjointness is <code>hdw</code>; the witness state is “write into the big heap”; the execution needs the cell to exist in the big heap, which is <code>union_of_some hFrame hl'</code>; the store equation is <code>rfl</code> (a write does not touch the store); the heap equation is the last <code>?_</code>."
        },
        {
          "tac": "show Heap.write (Heap.union h hFrame) l (e.eval σ)\n       = Heap.union (Heap.write h l (e.eval σ)) hFrame",
          "h": "The remaining goal is that equation with <code>State.heap</code> projections on both sides. <code>show</code> replaces a goal by any definitionally equal one; here it strips the projections so that the rewriting lemmas will match syntactically. Skipping this is the single most common way to get stuck in this proof."
        },
        {
          "tac": "funext x",
          "h": "Both sides are heaps, i.e. functions <code>Loc → Option Val</code>. Function extensionality is not automatic in Lean’s definitional equality, so you invoke it explicitly to reduce to a pointwise statement at an arbitrary <code>x</code>."
        },
        {
          "tac": "by_cases hxl : x = l",
          "h": "The written cell versus everything else."
        },
        {
          "tac": "· subst hxl",
          "h": "Again <code>l</code> is replaced by <code>x</code>. Watch the goal: every mention of <code>l</code>, including inside <code>hl'</code> and <code>hdw</code>, is now about <code>x</code>."
        },
        {
          "tac": "rw [write_same (Heap.union h hFrame) x (e.eval σ),\n    union_of_some hFrame (write_same h x (e.eval σ))]",
          "h": "Two rewrites in one bracket, applied left to right. The first turns the left-hand side into <code>some (e.eval σ)</code>. The second turns the right-hand side into <code>some (e.eval σ)</code>, using <code>write_same h x _ : Heap.write h x v x = some v</code> as the “the left heap has this cell” premise of <code>union_of_some</code>. Both sides now read <code>some (e.eval σ)</code> and <code>rw</code> closes the goal by <code>rfl</code>."
        },
        {
          "tac": "· rw [write_other (Heap.union h hFrame) l x (e.eval σ) hxl]",
          "h": "Off the written cell. The left-hand side becomes <code>Heap.union h hFrame x</code>."
        },
        {
          "tac": "have hwx : Heap.write h l (e.eval σ) x = h x := write_other h l x (e.eval σ) hxl",
          "h": "The same fact about the <i>small</i> heap, saved under a name because it is needed inside both branches of the next split."
        },
        {
          "tac": "cases hx : h x with",
          "h": "This is <code>cases</code> applied to an <i>expression</i>, not to a hypothesis: it splits on the two constructors of <code>Option Val</code>, giving branches named <code>none</code> and <code>some w</code>. The <code>hx :</code> prefix is what makes the split useful — it introduces <code>hx : h x = none</code> in one branch and <code>hx : h x = some w</code> in the other. Omit it and the branches are indistinguishable; see the aside below."
        },
        {
          "tac": "| none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]",
          "h": "Both sides fall through to <code>hFrame x</code>. On the right the premise needed is <code>Heap.write h l (e.eval σ) x = none</code>, which is <code>hwx</code> followed by <code>hx</code> — that is what <code>hwx.trans hx</code> means: <code>Eq.trans</code> in dot notation, composing <code>a = b</code> with <code>b = c</code>."
        },
        {
          "tac": "| some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]",
          "h": "Identical, with the other lemma: both sides are <code>some w</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "heapLocal_write, the interesting states",
          "start": "l : Loc\ne : Atom\n⊢ HeapLocal (Cmd.write l e)",
          "steps": [
            {
              "tac": "intro σ h hFrame s' hd hex\ncases hex with | write hl =>",
              "state": "case write\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\n⊢ { store := { store := σ, heap := h }.store,\n            heap := { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.heap.disjoint\n      hFrame ∧\n    ∃ r,\n      Exec (Cmd.write l e) { store := σ, heap := h.union hFrame } r ∧\n        r.store =\n            { store := { store := σ, heap := h }.store,\n                heap := { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.store ∧\n          r.heap =\n            { store := { store := σ, heap := h }.store,\n                    heap :=\n                      { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.heap.union\n              hFrame",
              "h": "This is what a goal looks like when nothing has been cleaned up. Every occurrence of <code>σ</code> and <code>h</code> is wrapped in a projection out of the state you never actually built. Nothing is wrong; it is just unreadable. Two tactics below — <code>have hl'</code> and <code>show</code> — exist entirely to get out of this."
            },
            {
              "tac": "intro x   (inside the hdw block)",
              "state": "l : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nx : Loc\n⊢ h.write l (Atom.eval σ e) x = none ∨ hFrame x = none",
              "h": "A clean, small goal, because you stated <code>hdw</code>’s type yourself. Note <code>hl' : h l = some old✝</code> sitting next to the projection-laden <code>hl</code>: same fact, usable form."
            },
            {
              "tac": "rcases hd x with hx | hx; by_cases hxl : x = l",
              "state": "case pos\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nx : Loc\nhx : h x = none\nhxl : x = l\n⊢ h.write l (Atom.eval σ e) x = none ∨ hFrame x = none",
              "h": "The contradiction branch. You have <code>hx : h x = none</code>, <code>hxl : x = l</code> and <code>hl' : h l = some old✝</code>. Substituting <code>x</code> for <code>l</code> and rewriting collides <code>none</code> with <code>some old✝</code>. In words: this is the branch where <code>hd</code> chose “the small heap is empty at <code>x</code>”, but <code>x</code> is the cell being written, and <code>Exec.write</code>’s side condition says the small heap owns it. Both cannot hold, so the branch is vacuous — and that is <i>why</i> the frame must be the empty one at <code>l</code>, which is what the other disjunct gives you."
            },
            {
              "tac": "(after the refine)",
              "state": "case write\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nhdw : (h.write l (Atom.eval σ e)).disjoint hFrame\n⊢ { store := σ, heap := (h.union hFrame).write l (Atom.eval σ e) }.heap =\n    { store := { store := σ, heap := h }.store,\n            heap := { store := σ, heap := h }.heap.write l (Atom.eval { store := σ, heap := h }.store e) }.heap.union\n      hFrame",
              "h": "One goal left, and it is the heap equation — but look at it. The left side is <code>{ store := σ, heap := (h.union hFrame).write l … }.heap</code>. No lemma in the library matches that."
            },
            {
              "tac": "show … ; funext x",
              "state": "case write\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nhdw : (h.write l (Atom.eval σ e)).disjoint hFrame\nx : Loc\n⊢ (h.union hFrame).write l (Atom.eval σ e) x = (h.write l (Atom.eval σ e)).union hFrame x",
              "h": "After <code>show</code> and <code>funext</code> the goal is finally a statement about heaps evaluated at a point, in exactly the vocabulary of <code>write_same</code>, <code>write_other</code>, <code>union_of_some</code>, <code>union_of_none</code>."
            },
            {
              "tac": "by_cases hxl : x = l; subst hxl",
              "state": "case pos\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nx : Loc\nhl : { store := σ, heap := h }.heap x = some old✝\nhl' : h x = some old✝\nhdw : (h.write x (Atom.eval σ e)).disjoint hFrame\n⊢ (h.union hFrame).write x (Atom.eval σ e) x = (h.write x (Atom.eval σ e)).union hFrame x",
              "h": "Read this one carefully: <code>l</code> has <i>vanished</i>. <code>subst</code> on <code>hxl : x = l</code> rewrote <code>l</code> to <code>x</code> throughout, including in <code>hl'</code> and <code>hdw</code>. That is why the following <code>rw</code> mentions <code>x</code>, not <code>l</code>: <code>write_same (Heap.union h hFrame) x (e.eval σ)</code>."
            },
            {
              "tac": "(neg branch, after rw and have hwx)",
              "state": "case neg\nl : Loc\ne : Atom\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nold✝ : Val\nhl : { store := σ, heap := h }.heap l = some old✝\nhl' : h l = some old✝\nhdw : (h.write l (Atom.eval σ e)).disjoint hFrame\nx : Loc\nhxl : ¬x = l\nhwx : h.write l (Atom.eval σ e) x = h x\n⊢ h.union hFrame x = (h.write l (Atom.eval σ e)).union hFrame x",
              "h": "The left side is now plain <code>h.union hFrame x</code> and the right side is the union of the written heap. <code>hwx</code> says the written heap agrees with <code>h</code> at <code>x</code>. Splitting on <code>h x</code> finishes both."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "state",
          "src": "error: Tactic `rewrite` failed: Did not find an occurrence of the pattern\n  (h.union hFrame).write x (Atom.eval σ e) x\nin the target expression\n  { store := σ, heap := (h.union hFrame).write x (Atom.eval σ e) }.heap x =\n    { store := { store := σ, heap := h }.store,\n            heap := { store := σ, heap := h }.heap.write x (Atom.eval { store := σ, heap := h }.store e) }.heap.union\n      hFrame x",
          "cap": "what Lean says if you go straight from the refine to funext, skipping the show"
        },
        {
          "t": "cmp",
          "left": {
            "t": "Without the <code>show</code>",
            "kind": "bad",
            "h": "The goal is the same proposition, but written with <code>State.heap</code> projections around both sides. <code>rw [write_same …]</code> looks for the literal subterm <code>(h.union hFrame).write x (Atom.eval σ e) x</code>, does not find it, and stops. Nothing you can do to the <i>proof</i> helps; the goal has to change shape."
          },
          "right": {
            "t": "With the <code>show</code>",
            "kind": "good",
            "h": "The goal is definitionally the same, but now it is <i>syntactically</i> what <code>write_same</code> is about, so <code>rw</code> finds its pattern. <code>show</code> costs nothing at runtime; it is a re-statement, not a step."
          }
        },
        {
          "t": "detail",
          "title": "The <code>have h' : … = _ := h</code> idiom, in general",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "This idiom appears twice in the chapter and is worth internalising. You have a hypothesis <code>h : A</code>; you want the same fact but with type <code>B</code>, where <code>A</code> and <code>B</code> are definitionally equal but not syntactically equal. Write <code>have h' : B := h</code>. Lean elaborates <code>h</code> against the expected type <code>B</code>, the definitional check succeeds, and you now have a hypothesis whose <i>displayed</i> type is <code>B</code> — which is what <code>rw</code>, <code>simp</code> and pattern matching care about."
            },
            {
              "t": "p",
              "h": "The <code>_</code> is a convenience: you only need to pin down the part that is causing trouble (here the left-hand side <code>h l</code>), and Lean infers the rest from <code>hl</code>. Writing <code>have hl' : h l = some old✝ := hl</code> would fail for a different reason — you cannot type the name <code>old✝</code>."
            },
            {
              "t": "p",
              "h": "In term position the same effect is available as <code>show B from h</code>. Bare type ascription is <i>not</i> a substitute: <code>have h₃ := (hl : h l = _)</code> leaves <code>h₃</code> with the projection still on it, because the ascription is discharged by unification and the term handed back is <code>hl</code> unchanged. <code>have h' : B := h</code> is the form that leaves a named hypothesis whose displayed type is the one you asked for, which is what <code>rw</code> reads."
            }
          ]
        },
        {
          "t": "detail",
          "title": "Why <code>cases hx : h x</code> and not <code>cases h x</code>",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Write <code>cases h x with | none => … | some w => …</code> and Lean accepts it. Here is the <code>none</code> branch:"
            },
            {
              "t": "state",
              "src": "case neg.none\nh hFrame : Heap\nl : Loc\nv : Val\nx : Loc\nhxl : ¬x = l\nhwx : h.write l v x = h x\n⊢ h.union hFrame x = (h.write l v).union hFrame x",
              "cap": "after cases h x, without the hx: label"
            },
            {
              "t": "p",
              "h": "The branch name says <code>none</code>, and that is the only trace of the split: the goal is untouched and <code>hwx</code> still says <code>h x</code>. Nothing in the context asserts <code>h x = none</code>, so <code>union_of_none hFrame ?</code> has no premise to take. The split happened and bought you nothing."
            },
            {
              "t": "p",
              "h": "The reason is that <code>cases e</code> abstracts <code>e</code> out of the <b>goal</b> and substitutes each constructor there; it does not touch hypotheses, and it does not record what it assumed. Here <code>rw [write_other …]</code> had already left the goal in terms of <code>h.union hFrame x</code>, with no occurrence of <code>h x</code> at all — so there was nothing to substitute into and the split evaporated. <code>cases hx : e</code> exists exactly for this: it hypothesises the equation instead of substituting it, and the equation is what <code>union_of_none</code> and <code>union_of_some</code> take as their premise."
            }
          ]
        },
        {
          "t": "detail",
          "title": "The heap equation on its own",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "It is worth pulling the second half out and seeing that it needs <i>no</i> hypotheses — not disjointness, not that <code>h</code> owns <code>l</code>:"
            },
            {
              "t": "code",
              "tag": "illustration",
              "src": "-- the heap equation half of heapLocal_write needs no disjointness at all\ntheorem write_union_no_disjointness (h hFrame : Heap) (l : Loc) (v : Val) :\n    Heap.write (Heap.union h hFrame) l v = Heap.union (Heap.write h l v) hFrame := by\n  funext x\n  by_cases hxl : x = l\n  · subst hxl\n    rw [write_same (Heap.union h hFrame) x v, union_of_some hFrame (write_same h x v)]\n  · rw [write_other (Heap.union h hFrame) l x v hxl]\n    have hwx : Heap.write h l v x = h x := write_other h l x v hxl\n    cases hx : h x with\n    | none => rw [union_of_none hFrame hx, union_of_none hFrame (hwx.trans hx)]\n    | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hwx.trans hx)]",
              "cap": "not in the corpus — compiles against prelude/m8.lean"
            },
            {
              "t": "p",
              "h": "So all of the side conditions in <code>heapLocal_write</code> are there for the <i>other</i> two obligations: <code>h l = some old</code> is needed to run the write on the big heap at all, and disjointness is needed for the domain conjunct. The equation itself is a pure fact about <code>write</code> and left-biased union. Compare <code>free</code>, where the corresponding equation is false without disjointness."
            }
          ]
        }
      ],
      "pitfall": "You will skip <code>have hl'</code> and write <code>rw [hl] at hx</code>. Lean answers, in full:<br><code>Tactic `rewrite` failed: Did not find an occurrence of the pattern { store := σ, heap := h }.heap x in the target expression h x = none</code>. The message is telling the exact truth and is still easy to misread: it is not saying the fact is wrong, it is saying the <i>syntax</i> does not occur. Definitional equality does not help <code>rw</code>. The same trap fires again after the <code>refine</code>, where the fix is <code>show</code> rather than <code>have</code>.",
      "variants": "Delete <code>hd</code> and exactly one thing breaks: the first conclusion, <code>Heap.disjoint (Heap.write h l v) hFrame</code>. Concretely, take <code>h = Heap.singleton 0 7</code> and <code>hFrame = Heap.singleton 0 99</code>, which are not disjoint, and run <code>.write 0 (.const 5)</code>: the resulting heap still owns <code>0</code>, so it still overlaps the frame, and the conjunct is false. The heap <i>equation</i>, by contrast, survives untouched — see the illustration above, which proves it with no hypothesis at all. That asymmetry is worth holding on to: for <code>write</code>, disjointness is needed only to keep the bookkeeping honest, whereas for <code>free</code> (the next exercise) it is needed for the equation itself. Reverse the union to <code>Heap.union hFrame h</code> and the <code>Exec.write</code> side condition breaks instead: <code>union_of_some hFrame hl'</code> no longer applies, because the left-biased union would consult the frame first."
    },
    {
      "t": "ex",
      "id": "m8-3",
      "name": "heapLocal_free",
      "hard": true,
      "why": "The one command that removes a cell, and therefore the one place where the frame’s disjointness does load-bearing work rather than bookkeeping. In <code>write</code> the two heaps never really interact; in <code>free</code> they do, and if you get the disjointness argument wrong the theorem is simply false.",
      "setup": "In scope: <code>erase_same : Heap.erase h l l = none</code> and <code>erase_other : x ≠ l → Heap.erase h l x = h x</code>, plus the union lemmas. <code>Heap.erase</code> is defined as <code>fun x => if x = l then none else h x</code>, so it shrinks the domain by exactly one cell.",
      "goal": "theorem heapLocal_free (l : Loc) : HeapLocal (.free l)",
      "hints": [
        "Same shape as <code>write</code>: a <code>have</code> for the disjointness, then a <code>refine</code>, then <code>show</code> + <code>funext</code> + a split on <code>x = l</code>. Copy that skeleton first and fill in the branches.",
        "The disjointness half is <i>easier</i> than for <code>write</code>: erasing only ever turns values into <code>none</code>, so the left disjunct is always available. That is why the proof says <code>left</code> before splitting on <code>x = l</code>, rather than after.",
        "The interesting branch is <code>x = l</code> in the heap equation. On the left, <code>erase_same</code> gives <code>none</code>. On the right, <code>union_of_none hFrame (erase_same h x)</code> says the union falls through to <code>hFrame x</code>. So the goal becomes <code>none = hFrame x</code>: you must prove the frame does not own the freed cell.",
        "That last step is where disjointness enters: <code>rcases hd x</code>. The branch where <code>h x = none</code> contradicts <code>hl' : h x = some v✝</code>; the branch where <code>hFrame x = none</code> is the goal up to <code>.symm</code>."
      ],
      "sol": "theorem heapLocal_free (l : Loc) : HeapLocal (.free l) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | free hl =>\n      have hl' : h l = _ := hl\n      have hde : Heap.disjoint (Heap.erase h l) hFrame := by\n        intro x\n        rcases hd x with hx | hx\n        · left\n          by_cases hxl : x = l\n          · subst hxl; exact erase_same h x\n          · rw [erase_other h l x hxl]; exact hx\n        · exact Or.inr hx\n      refine ⟨hde, ⟨σ, Heap.erase (Heap.union h hFrame) l⟩,\n              Exec.free (union_of_some hFrame hl'), rfl, ?_⟩\n      show Heap.erase (Heap.union h hFrame) l = Heap.union (Heap.erase h l) hFrame\n      funext x\n      by_cases hxl : x = l\n      · subst hxl\n        rw [erase_same (Heap.union h hFrame) x,\n            union_of_none hFrame (erase_same h x)]\n        rcases hd x with hx | hx\n        · rw [hx] at hl'; exact absurd hl' (by simp)\n        · exact hx.symm\n      · rw [erase_other (Heap.union h hFrame) l x hxl]\n        have hex' : Heap.erase h l x = h x := erase_other h l x hxl\n        cases hx : h x with\n        | none => rw [union_of_none hFrame hx, union_of_none hFrame (hex'.trans hx)]\n        | some w => rw [union_of_some hFrame hx, union_of_some hFrame (hex'.trans hx)]",
      "expl": "This is the case where the two heaps genuinely interact. Because <code>h l = some v</code>, disjointness forces <code>hFrame l = none</code>; so erasing <code>l</code> from the union really does yield <code>none</code> there, matching <code>(erase h l) ∪ hFrame</code>. If the frame were allowed to own <code>l</code> too, freeing would silently reveal the frame’s value — and locality would fail.",
      "walk": [
        {
          "tac": "intro σ h hFrame s' hd hex",
          "h": "The six binders."
        },
        {
          "tac": "cases hex with",
          "h": "Named form for the side condition."
        },
        {
          "tac": "| free hl =>",
          "h": "Binds <code>hl : { store := σ, heap := h }.heap l = some v✝</code> and fixes <code>s' = ⟨σ, Heap.erase h l⟩</code>."
        },
        {
          "tac": "have hl' : h l = _ := hl",
          "h": "Same projection-stripping move as in the write case, and needed for the same reason: <code>hl</code> is about a projection, <code>rw</code> is syntactic."
        },
        {
          "tac": "have hde : Heap.disjoint (Heap.erase h l) hFrame := by",
          "h": "Obligation (a): the erased heap is still disjoint from the frame."
        },
        {
          "tac": "intro x",
          "h": "Fix a location."
        },
        {
          "tac": "rcases hd x with hx | hx",
          "h": "Split the assumption at <code>x</code>."
        },
        {
          "tac": "· left",
          "h": "In the first branch we will prove the left disjunct, <code>Heap.erase h l x = none</code>. Choosing <i>before</i> the case split works here because erasing never creates a value — unlike <code>write</code>, where the choice depended on the branch."
        },
        {
          "tac": "by_cases hxl : x = l",
          "h": "At the erased cell or elsewhere."
        },
        {
          "tac": "· subst hxl; exact erase_same h x",
          "h": "At the erased cell the answer is <code>none</code> by definition. <code>subst</code> again replaces <code>l</code> by <code>x</code>, so the lemma is applied as <code>erase_same h x</code>."
        },
        {
          "tac": "· rw [erase_other h l x hxl]; exact hx",
          "h": "Elsewhere nothing changed, so <code>hx : h x = none</code> is already the goal."
        },
        {
          "tac": "· exact Or.inr hx",
          "h": "Second branch: the frame is empty at <code>x</code>, which is the right disjunct unchanged."
        },
        {
          "tac": "refine ⟨hde, ⟨σ, Heap.erase (Heap.union h hFrame) l⟩,\n        Exec.free (union_of_some hFrame hl'), rfl, ?_⟩",
          "h": "Five components. The witness state erases <code>l</code> from the big heap; <code>Exec.free</code> needs the cell to exist there, supplied by <code>union_of_some</code>; the store is untouched so <code>rfl</code>; the heap equation is left open."
        },
        {
          "tac": "show Heap.erase (Heap.union h hFrame) l = Heap.union (Heap.erase h l) hFrame",
          "h": "Strip the projections so the erase/union lemmas can match. Same reason as before."
        },
        {
          "tac": "funext x",
          "h": "Reduce equality of heaps to equality at each location."
        },
        {
          "tac": "by_cases hxl : x = l",
          "h": "The freed cell versus everything else."
        },
        {
          "tac": "· subst hxl",
          "h": "<code>l</code> becomes <code>x</code> everywhere, including in <code>hl'</code> and <code>hde</code>."
        },
        {
          "tac": "rw [erase_same (Heap.union h hFrame) x,\n    union_of_none hFrame (erase_same h x)]",
          "h": "Left side: erasing at the erased cell gives <code>none</code>. Right side: the small heap is <code>none</code> there, so the left-biased union falls through to the frame. The goal is now <code>none = hFrame x</code> — a statement purely about the frame."
        },
        {
          "tac": "rcases hd x with hx | hx",
          "h": "And this is the moment. To finish you need <code>hFrame x = none</code>, and the <i>only</i> source of that is disjointness."
        },
        {
          "tac": "· rw [hx] at hl'; exact absurd hl' (by simp)",
          "h": "The branch where <code>h x = none</code> is impossible: <code>hl'</code> says the command owned that cell, so <code>h x = some v✝</code>. Rewriting turns <code>hl'</code> into <code>none = some v✝</code>, and <code>simp</code> refutes it."
        },
        {
          "tac": "· exact hx.symm",
          "h": "The branch that survives. <code>hx : hFrame x = none</code>, the goal is <code>none = hFrame x</code>, so <code>.symm</code> — <code>Eq.symm</code> in dot notation. Getting the direction wrong here is a classic five-minute loss."
        },
        {
          "tac": "· rw [erase_other (Heap.union h hFrame) l x hxl]",
          "h": "Off the freed cell: erasing changed nothing on the left, so the left side is <code>Heap.union h hFrame x</code>."
        },
        {
          "tac": "have hex' : Heap.erase h l x = h x := erase_other h l x hxl",
          "h": "The same fact about the small heap, named for use in both branches of the next split."
        },
        {
          "tac": "cases hx : h x with",
          "h": "Split on whether the small heap owns <code>x</code>, recording the equation as <code>hx</code>."
        },
        {
          "tac": "| none => rw [union_of_none hFrame hx, union_of_none hFrame (hex'.trans hx)]",
          "h": "Both unions fall through to <code>hFrame x</code>. <code>hex'.trans hx</code> chains <code>Heap.erase h l x = h x</code> with <code>h x = none</code>."
        },
        {
          "tac": "| some w => rw [union_of_some hFrame hx, union_of_some hFrame (hex'.trans hx)]",
          "h": "Both unions return <code>some w</code>."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "heapLocal_free, the interesting states",
          "start": "l : Loc\n⊢ HeapLocal (Cmd.free l)",
          "steps": [
            {
              "tac": "intro σ h hFrame s' hd hex\ncases hex with | free hl =>",
              "state": "case free\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\n⊢ { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap.disjoint hFrame ∧\n    ∃ r,\n      Exec (Cmd.free l) { store := σ, heap := h.union hFrame } r ∧\n        r.store = { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.store ∧\n          r.heap =\n            { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap.union\n              hFrame",
              "h": "The usual projection soup. <code>s'</code> is gone, replaced by <code>⟨σ, Heap.erase h l⟩</code> written out."
            },
            {
              "tac": "(inside hde, pos branch)",
              "state": "case pos\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhl' : h l = some v✝\nx : Loc\nhx : h x = none\nhxl : x = l\n⊢ h.erase l x = none",
              "h": "Goal <code>h.erase l x = none</code> with <code>hxl : x = l</code>. Notice the goal is <i>only</i> the left disjunct — because <code>left</code> was applied before the split. There is no contradiction to find here; erasing at <code>l</code> genuinely gives <code>none</code>."
            },
            {
              "tac": "(after the refine)",
              "state": "case free\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhl' : h l = some v✝\nhde : (h.erase l).disjoint hFrame\n⊢ { store := σ, heap := (h.union hFrame).erase l }.heap =\n    { store := { store := σ, heap := h }.store, heap := { store := σ, heap := h }.heap.erase l }.heap.union hFrame",
              "h": "The heap equation, wrapped. <code>hde</code> is in context and discharged the first conjunct."
            },
            {
              "tac": "show …; funext x; by_cases hxl : x = l; subst hxl",
              "state": "case pos\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nx : Loc\nhl : { store := σ, heap := h }.heap x = some v✝\nhl' : h x = some v✝\nhde : (h.erase x).disjoint hFrame\n⊢ (h.union hFrame).erase x x = (h.erase x).union hFrame x",
              "h": "Clean, and <code>l</code> has been replaced by <code>x</code> everywhere by the <code>subst</code>."
            },
            {
              "tac": "rw [erase_same …, union_of_none …]",
              "state": "case pos\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nx : Loc\nhl : { store := σ, heap := h }.heap x = some v✝\nhl' : h x = some v✝\nhde : (h.erase x).disjoint hFrame\n⊢ none = hFrame x",
              "h": "<b>This is the whole theorem in one line.</b> Erasing the cell from the union left <code>none</code> there; the reassembled heap <code>(erase h l) ∪ hFrame</code> reads <code>hFrame x</code> there. They agree exactly when the frame does not own <code>x</code> — and it does not, because the command did, and the two are disjoint. Every other line of this proof is bookkeeping around this one goal."
            },
            {
              "tac": "(neg branch, after rw and have hex')",
              "state": "case neg\nl : Loc\nσ : Store\nh hFrame : Heap\nhd : h.disjoint hFrame\nv✝ : Val\nhl : { store := σ, heap := h }.heap l = some v✝\nhl' : h l = some v✝\nhde : (h.erase l).disjoint hFrame\nx : Loc\nhxl : ¬x = l\nhex' : h.erase l x = h x\n⊢ h.union hFrame x = (h.erase l).union hFrame x",
              "h": "Away from the freed cell nothing interesting happens; both sides are unions that agree because <code>Heap.erase h l</code> agrees with <code>h</code> at <code>x</code>."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The mathematical content, stripped of Lean",
          "items": [
            {
              "k": "Claim",
              "h": "If <code>h ⊥ hFrame</code> and <code>l ∈ dom h</code>, then <code>(h ∪ hFrame) ∖ l = (h ∖ l) ∪ hFrame</code>."
            },
            {
              "k": "At l",
              "h": "Left: <code>l</code> was erased, so <code>none</code>. Right: <code>h ∖ l</code> is undefined at <code>l</code>, so the union defers to <code>hFrame l</code>. These agree <i>iff</i> <code>l ∉ dom hFrame</code>, which follows from <code>l ∈ dom h</code> and disjointness. <b>This is the only place the hypotheses are used.</b>"
            },
            {
              "k": "Away from l",
              "h": "Erasing does nothing on either side, so both reduce to <code>(h ∪ hFrame) x</code>. No hypothesis needed."
            },
            {
              "k": "Why write is easier",
              "h": "For <code>write</code> the corresponding point <code>l</code> gives <code>some v</code> on both sides regardless of the frame, so the disjointness is only needed for the <i>domain</i> conjunct, not for the equation. <code>free</code> needs it for both."
            }
          ]
        }
      ],
      "pitfall": "The direction of the final equality. After the two rewrites the goal is <code>none = hFrame x</code> and your hypothesis is <code>hx : hFrame x = none</code>. <code>exact hx</code> fails with a type mismatch that looks like nonsense until you read it twice. The fix is <code>hx.symm</code>. The reason the goal comes out backwards is that <code>rw</code> rewrote the left-hand side of the equation to <code>none</code> and left the right-hand side alone; there is no rule saying the goal must end up in the orientation you find natural.",
      "variants": "Let the frame own <code>l</code> too — i.e. drop <code>hd</code>. Concretely: <code>h = Heap.singleton 0 7</code>, <code>hFrame = Heap.singleton 0 99</code>, <code>c = .free 0</code>. The small run leaves <code>Heap.empty</code>, so the reassembled heap <code>Heap.empty ∪ hFrame</code> maps <code>0</code> to <code>99</code>. The big run starts from <code>h ∪ hFrame</code>, which maps <code>0</code> to <code>7</code>, and erases <code>0</code>, giving <code>none</code>. So <code>r.heap ≠ Heap.union s'.heap hFrame</code> at location <code>0</code>: locality fails. In program terms, freeing a cell you own would silently expose someone else’s value at the same address — which is exactly the bug separation logic exists to make impossible to state."
    },
    {
      "t": "ex",
      "id": "m8-4",
      "name": "heapLocal_seq",
      "hard": false,
      "why": "Locality is compositional — which is what makes it a usable side condition rather than a per-program obligation. It is also the exercise that justifies the disjointness conjunct: you need it in the middle of the sequence, and there is nowhere else to get it.",
      "setup": "In scope: <code>Exec.seq {s s' s'' c₁ c₂} (h₁ : Exec c₁ s s') (h₂ : Exec c₂ s' s'') : Exec (c₁ ;; c₂) s s''</code>. The middle state is implicit, which is the source of the one wrinkle in this proof.",
      "goal": "theorem heapLocal_seq {c₁ c₂ : Cmd} (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) :\n    HeapLocal (c₁ ;; c₂)",
      "hints": [
        "Apply <code>h₁</code> to get from the start to the middle, then <code>h₂</code> from the middle to the end, then glue the two lifted runs with <code>Exec.seq</code>.",
        "After <code>cases hex with | seq hex₁ hex₂</code> look at the context: the intermediate state is there, but it is called <code>s'✝</code> and you cannot type that. <code>rename_i sMid</code> gives it a name. <code>rename_i</code> names inaccessible hypotheses counting from the right, so with one argument it names the most recently introduced one.",
        "Applying <code>h₂</code> needs a disjointness hypothesis for the <i>middle</i> heap and the frame. That is <code>hdMid</code>, the first component of what <code>h₁</code> just gave you. This is the payoff for the extra conjunct in <code>HeapLocal</code>.",
        "Last wrinkle: <code>h₂</code> produced <code>Exec c₂ ⟨sMid.store, sMid.heap ∪ hFrame⟩ r₂</code>, but <code>Exec.seq hr₁ ?_</code> wants <code>Exec c₂ r₁ r₂</code>. Prove <code>heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩</code> by <code>rw [← hst₁, ← hhp₁]</code> — rewriting backwards turns the right-hand side into <code>⟨r₁.store, r₁.heap⟩</code>, and structure eta makes that <code>r₁</code>, closing the goal by <code>rfl</code>. Then <code>rw [heq]</code> in the main goal."
      ],
      "sol": "theorem heapLocal_seq {c₁ c₂ : Cmd} (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) :\n    HeapLocal (c₁ ;; c₂) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | seq hex₁ hex₂ =>\n      rename_i sMid\n      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁\n      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂\n      refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩\n      have heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩ := by\n        rw [← hst₁, ← hhp₁]\n      rw [heq]\n      exact hr₂",
      "expl": "Here is the payoff for adding the disjointness conjunct: <code>hdMid</code> comes out of the first application and goes straight into the second. Without it you would be stuck at the halfway point. The final wrinkle is that <code>h₂</code> gives you <code>Exec c₂ ⟨sMid.store, sMid.heap ∪ hFrame⟩ r₂</code> whereas you need <code>Exec c₂ r₁ r₂</code>; the <code>have heq : r₁ = ⟨…⟩</code> step closes that gap using structure eta.",
      "walk": [
        {
          "tac": "intro σ h hFrame s' hd hex",
          "h": "The six binders of <code>HeapLocal (c₁ ;; c₂)</code>. Note <code>h₁</code> and <code>h₂</code> — the locality assumptions for the two halves — were already bound as theorem arguments."
        },
        {
          "tac": "cases hex with",
          "h": "Only <code>Exec.seq</code> can produce an execution of a sequence."
        },
        {
          "tac": "| seq hex₁ hex₂ =>",
          "h": "Names the two sub-executions. The intermediate state is an <i>implicit</i> field of <code>Exec.seq</code>, so it is introduced but left inaccessible as <code>s'✝</code>."
        },
        {
          "tac": "rename_i sMid",
          "h": "Names it <code>sMid</code>. Without this you cannot instantiate <code>h₁</code> at the middle state, because you cannot write its name. <code>rename_i</code> takes names for the trailing inaccessible hypotheses, right to left."
        },
        {
          "tac": "obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁",
          "h": "Applies the first locality assumption to the first half of the run and destructures the result in one move: the middle disjointness, the lifted middle state, its execution, and the two equations. <code>obtain</code> is <code>rcases</code> with a <code>:=</code>; the five-component pattern mirrors the five components of <code>HeapLocal</code>’s conclusion."
        },
        {
          "tac": "obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂",
          "h": "Same for the second half, starting from the middle state and using <code>hdMid</code> as the disjointness hypothesis. <b>This is the line that would be impossible without the extra conjunct in <code>HeapLocal</code>.</b>"
        },
        {
          "tac": "refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩",
          "h": "The five components of the conclusion for the sequence: end disjointness from <code>h₂</code>, final state <code>r₂</code>, the glued execution, and the two equations, also from <code>h₂</code>. Only the second half of the glued execution is left open."
        },
        {
          "tac": "have heq : r₁ = ⟨sMid.store, Heap.union sMid.heap hFrame⟩ := by",
          "h": "The type mismatch <code>hr₂</code> has against the goal is purely about how the middle state is written. Prove they are the same state."
        },
        {
          "tac": "rw [← hst₁, ← hhp₁]",
          "h": "Rewriting <i>backwards</i> along the two equations replaces <code>sMid.store</code> by <code>r₁.store</code> and <code>sMid.heap.union hFrame</code> by <code>r₁.heap</code>, so the goal becomes <code>r₁ = ⟨r₁.store, r₁.heap⟩</code>. Lean closes that by <code>rfl</code> automatically: structure eta says a structure is definitionally its own field-by-field reconstruction."
        },
        {
          "tac": "rw [heq]",
          "h": "Rewrites the goal <code>Exec c₂ r₁ r₂</code> into <code>Exec c₂ ⟨sMid.store, sMid.heap ∪ hFrame⟩ r₂</code>."
        },
        {
          "tac": "exact hr₂",
          "h": "Which is exactly what <code>h₂</code> handed over."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "heapLocal_seq, tactic by tactic",
          "start": "c₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\n⊢ HeapLocal (c₁ ;; c₂)",
          "steps": [
            {
              "tac": "intro σ h hFrame s' hd hex\ncases hex with | seq hex₁ hex₂ =>",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\ns'✝ : State\nhex₁ : Exec c₁ { store := σ, heap := h } s'✝\nhex₂ : Exec c₂ s'✝ s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Look at <code>s'✝ : State</code>. It exists, both sub-executions mention it, and you cannot refer to it. That is the entire reason the next line exists."
            },
            {
              "tac": "rename_i sMid",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Same context, one name changed. Nothing mathematical happened; the proof simply became writable."
            },
            {
              "tac": "obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Five new hypotheses, matching the five conjuncts of <code>HeapLocal</code>’s conclusion. <code>hdMid : sMid.heap.disjoint hFrame</code> is the one to watch."
            },
            {
              "tac": "obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := h₂ sMid.store sMid.heap hFrame s' hdMid hex₂",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\nhdEnd : s'.heap.disjoint hFrame\nr₂ : State\nhr₂ : Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nhst₂ : r₂.store = s'.store\nhhp₂ : r₂.heap = s'.heap.union hFrame\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "h": "Five more. Everything the goal asks for is now in the context: <code>hdEnd</code>, <code>r₂</code>, <code>hst₂</code>, <code>hhp₂</code>. Only the execution has to be assembled."
            },
            {
              "tac": "refine ⟨hdEnd, r₂, Exec.seq hr₁ ?_, hst₂, hhp₂⟩",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\nhdEnd : s'.heap.disjoint hFrame\nr₂ : State\nhr₂ : Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nhst₂ : r₂.store = s'.store\nhhp₂ : r₂.heap = s'.heap.union hFrame\n⊢ Exec c₂ r₁ r₂",
              "h": "The context is unchanged — <code>refine</code> only consumed hypotheses, it did not introduce any — and there is one goal left. It is a mismatch of notation rather than of content: <code>hr₂</code> is about <code>{ store := sMid.store, heap := sMid.heap.union hFrame }</code> while the goal is about <code>r₁</code>."
            },
            {
              "tac": "have heq : … := by rw [← hst₁, ← hhp₁]\nrw [heq]",
              "state": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\nsMid : State\nhex₁ : Exec c₁ { store := σ, heap := h } sMid\nhex₂ : Exec c₂ sMid s'\nhdMid : sMid.heap.disjoint hFrame\nr₁ : State\nhr₁ : Exec c₁ { store := σ, heap := h.union hFrame } r₁\nhst₁ : r₁.store = sMid.store\nhhp₁ : r₁.heap = sMid.heap.union hFrame\nhdEnd : s'.heap.disjoint hFrame\nr₂ : State\nhr₂ : Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nhst₂ : r₂.store = s'.store\nhhp₂ : r₂.heap = s'.heap.union hFrame\nheq : r₁ = { store := sMid.store, heap := sMid.heap.union hFrame }\n⊢ Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂",
              "h": "And now <code>exact hr₂</code> closes it."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "detail",
          "title": "Why <code>exact hr₂</code> does not just work",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "It is tempting to think <code>r₁</code> and <code>⟨sMid.store, sMid.heap ∪ hFrame⟩</code> are the same by definition. They are not: <code>r₁</code> is an opaque variable, and all you know about it is the two <i>propositional</i> equalities <code>hst₁</code> and <code>hhp₁</code>. Definitional equality cannot see through a hypothesis. Try it and Lean says:"
            },
            {
              "t": "state",
              "src": "error: Type mismatch\n  hr₂\nhas type\n  Exec c₂ { store := sMid.store, heap := sMid.heap.union hFrame } r₂\nbut is expected to have type\n  Exec c₂ r₁ r₂",
              "cap": "what happens if you drop the have/rw"
            },
            {
              "t": "p",
              "h": "Structure eta is the part that <i>is</i> definitional: <code>r₁</code> and <code>⟨r₁.store, r₁.heap⟩</code> are interchangeable with no proof at all. So the job of <code>rw [← hst₁, ← hhp₁]</code> is to get the goal into that shape, at which point <code>rfl</code> fires by itself and the <code>have</code> block needs no further tactic."
            }
          ]
        },
        {
          "t": "detail",
          "title": "The <code>obtain</code> shortcut that silently does not work",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "Since <code>Exec.seq</code> has three fields — the middle state and the two sub-executions — it is natural to try <code>obtain ⟨sMid, hex₁, hex₂⟩ := hex</code> and skip the <code>rename_i</code>. Lean accepts the line without complaint. Here is the context immediately afterwards:"
            },
            {
              "t": "state",
              "src": "case seq\nc₁ c₂ : Cmd\nh₁ : HeapLocal c₁\nh₂ : HeapLocal c₂\nσ : Store\nh hFrame : Heap\ns' : State\nhd : h.disjoint hFrame\ns'✝ : State\nh₁✝ : Exec c₁ { store := σ, heap := h } s'✝\nh₂✝ : Exec c₂ s'✝ s'\n⊢ s'.heap.disjoint hFrame ∧\n    ∃ r, Exec (c₁ ;; c₂) { store := σ, heap := h.union hFrame } r ∧ r.store = s'.store ∧ r.heap = s'.heap.union hFrame",
              "cap": "after obtain ⟨sMid, hex₁, hex₂⟩ := hex"
            },
            {
              "t": "p",
              "h": "All three names were dropped, and the replacements are not arbitrary: <code>s'</code>, <code>h₁</code> and <code>h₂</code> are <code>Exec.seq</code>’s own field names — read the constructor in the setup above. A name already in scope is not overwritten, so Lean marks the <i>incoming</i> ones inaccessible. Your locality assumptions <code>h₁</code> and <code>h₂</code> therefore survive intact; that is why this line raises nothing at all."
            },
            {
              "t": "p",
              "h": "The bill arrives on the next line that uses a name you thought you had bound. <code>obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := h₁ σ h hFrame sMid hd hex₁</code> gets two errors at once:"
            },
            {
              "t": "state",
              "src": "error(lean.unknownIdentifier): Unknown identifier `sMid`\nerror(lean.unknownIdentifier): Unknown identifier `hex₁`",
              "cap": "reported at the use, not at the obtain"
            },
            {
              "t": "p",
              "h": "<code>cases … with | seq hex₁ hex₂</code> does name the explicit fields; only the implicit middle state needs <code>rename_i</code>."
            }
          ]
        }
      ],
      "pitfall": "The obvious shortcut is <code>obtain ⟨sMid, hex₁, hex₂⟩ := hex</code> — destructure the execution and name the middle state in one go. It <i>reports no error</i>, which is the trap. Look at the context afterwards — the aside below shows it — and every name you asked for has been silently dropped, leaving three inaccessible hypotheses instead of one. The next line that mentions <code>sMid</code> or <code>hex₁</code> then fails with <code>Unknown identifier</code>, and the error is reported at the <i>use</i>, saying nothing about the <code>obtain</code> that swallowed the names — so you go looking at the wrong line. Use <code>cases … with | seq hex₁ hex₂</code>, which names the two explicit fields properly, and then <code>rename_i sMid</code> for the implicit one. Writing <code>s'✝</code> by hand is not an option either: <code>✝</code> is not an input character.",
      "variants": "Remove the <code>Heap.disjoint s'.heap hFrame</code> conjunct from <code>HeapLocal</code> and this proof dies at the second <code>obtain</code>: <code>h₂</code> demands a disjointness proof for <code>sMid.heap</code> and <code>hFrame</code>, you have one only for the <i>initial</i> heap, and no lemma converts between them (there cannot be one — it is exactly the fact that got deleted). Reverse the two locality assumptions — apply <code>h₂</code> first — and you get nowhere, because the second command’s run starts at a state you have not yet produced. And note what is <i>not</i> needed: nothing about <code>c₁</code> and <code>c₂</code> individually, no determinism, no termination. Locality composes for the same reason simulations compose."
    },
    {
      "t": "sec",
      "s": "Exercise · the frame theorem"
    },
    {
      "t": "ex",
      "id": "m8-5",
      "name": "hoare_frame",
      "hard": true,
      "why": "<b>The theorem the whole course exists to prove.</b> Eight lines, and every one of them is a step of the informal argument you sketched at the top of the chapter. Once it is proved, the rest of the workbook is composition.",
      "setup": "Everything is already available. <code>Hoare P c Q</code> unfolds to <code>∀ σ h, P σ h → ∃ s', Exec c ⟨σ, h⟩ s' ∧ Q s'.store s'.heap</code>, and <code>(P ∗ R) σ h</code> unfolds to <code>∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ R σ h₂</code>. No lemma about <code>∗</code> from M4 is needed — you go through the definition.",
      "goal": "theorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R)",
      "hints": [
        "Start by unfolding both sides by hand: <code>intro σ h hstar</code>, then destructure <code>hstar</code> with the six-component star pattern from M4.",
        "Now follow the plan. <code>hc σ hP hp</code> is “run it small”. <code>hlocal σ hP hR s' hd hex</code> is “lift it”. Both are just applications — the hypotheses are literally the things you have.",
        "Before assembling, get rid of <code>hu : h = hP.union hR</code> with <code>subst hu</code>. If you do not, the goal still mentions <code>h</code> while the lifted execution mentions <code>hP.union hR</code>, and the <code>refine</code> will fail on an application type mismatch.",
        "The final <code>refine</code> takes eight components: <code>⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩</code>. Read them as “the state, its execution, then the cut <code>s'.heap</code> / <code>hR</code>, their disjointness, the union equation, and the two halves of the star”. The union equation you need is <code>r.heap = Heap.union s'.heap hR</code> — which is exactly <code>hrhp</code>.",
        "Goal 1 is <code>Q r.store s'.heap</code> and you have <code>hq : Q s'.store s'.heap</code>; <code>rw [hrst]</code> bridges them. Goal 2 is <code>R r.store hR</code> — which is what <code>Preserves</code> was defined to give you: <code>hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr</code>."
      ],
      "sol": "theorem hoare_frame {P Q R : Assertion} {c : Cmd}\n    (hc : Hoare P c Q) (hlocal : HeapLocal c) (hpres : Preserves c R) :\n    Hoare (P ∗ R) c (Q ∗ R) := by\n  intro σ h hstar\n  obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar\n  obtain ⟨s', hex, hq⟩ := hc σ hP hp\n  obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex\n  subst hu\n  refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩\n  · rw [hrst]; exact hq\n  · exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",
      "expl": "The proof is eight lines and each one is a step of the informal argument. <code>hc σ hP hp</code> is “run it small”. <code>hlocal σ hP hR s' hd hex</code> is “lift it”. The <code>refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩</code> line is the reassembly: final state <code>r</code>, its execution, and the cut <code>s'.heap</code> / <code>hR</code>. The two remaining goals are <code>Q</code> at the new store (immediate, since <code>hrst : r.store = s'.store</code>) and <code>R</code> at the new store (this is <i>exactly</i> what <code>Preserves</code> was invented for). Nothing is hidden and nothing is assumed.",
      "walk": [
        {
          "tac": "intro σ h hstar",
          "h": "Unfolds the <code>Hoare</code> in the conclusion. You now owe an execution and a postcondition, given that <code>P ∗ R</code> holds of <code>h</code>."
        },
        {
          "tac": "obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar",
          "h": "<b>Step 1, split.</b> The six components of <code>star</code>: the two heaps, their disjointness, the union equation, and the two assertions. This is the pattern you have used since M4."
        },
        {
          "tac": "obtain ⟨s', hex, hq⟩ := hc σ hP hp",
          "h": "<b>Step 2, run it small.</b> Feed the <i>small</i> heap <code>hP</code> and the proof <code>hp : P σ hP</code> to the triple you were given. Out comes a final state <code>s'</code>, an execution on the small heap, and <code>Q</code> of that state."
        },
        {
          "tac": "obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex",
          "h": "<b>Step 3, lift it.</b> Locality takes the small run and the frame <code>hR</code> and returns everything you need about the big run: the end disjointness <code>hdEnd</code>, the big final state <code>r</code>, its execution, and the two equations. Note the frame here is <code>hR</code> — the <i>heap</i> that <code>R</code> describes, not <code>R</code> itself."
        },
        {
          "tac": "subst hu",
          "h": "Replaces <code>h</code> by <code>hP.union hR</code> everywhere, including in the goal. Now the goal’s execution and <code>hrex</code> talk about the same starting heap."
        },
        {
          "tac": "refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩",
          "h": "<b>Step 4, reassemble.</b> Eight components flattened from <code>∃ s', Exec ∧ (∃ h₁ h₂, disjoint ∧ eq ∧ Q ∧ R)</code>. The creative choice is the cut: the <code>Q</code>-part is <code>s'.heap</code> (the small run’s final heap) and the <code>R</code>-part is <code>hR</code> (untouched). <code>hrhp : r.heap = s'.heap.union hR</code> is precisely the union equation the star demands — the locality conclusion was designed to be exactly this."
        },
        {
          "tac": "· rw [hrst]; exact hq",
          "h": "Goal 1 is <code>Q r.store s'.heap</code>. <code>hrst : r.store = s'.store</code> rewrites it to <code>Q s'.store s'.heap</code>, which is <code>hq</code>. In words: the frame did not change what the command did to the store, so <code>Q</code> still holds."
        },
        {
          "tac": "· exact hpres ⟨σ, Heap.union hP hR⟩ r hrex hR hr",
          "h": "<b>Step 5, re-establish R.</b> Goal 2 is <code>R r.store hR</code>: the frame’s heap is untouched but the store has moved. <code>Preserves</code> takes the initial state, the final state, the execution between them, the frame heap, and <code>R</code> at the old store, and returns <code>R</code> at the new one. Note you have to build the initial state by hand as <code>⟨σ, Heap.union hP hR⟩</code>, because <code>Preserves</code> is stated about states, not about a store-and-heap pair."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "hoare_frame, tactic by tactic",
          "start": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\n⊢ Hoare (P ∗ R) c (Q ∗ R)",
          "steps": [
            {
              "tac": "intro σ h hstar",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh : Heap\nhstar : (P ∗ R) σ h\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "The goal is the unfolded <code>Hoare</code>: produce a final state, an execution from <code>⟨σ, h⟩</code>, and <code>Q ∗ R</code> of it."
            },
            {
              "tac": "obtain ⟨hP, hR, hd, hu, hp, hr⟩ := hstar",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "The star is gone from the hypotheses and its six pieces are in the context. Nothing about the goal changed."
            },
            {
              "tac": "obtain ⟨s', hex, hq⟩ := hc σ hP hp",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "<code>hex : Exec c { store := σ, heap := hP } s'</code> — the run on the small heap. The goal wants a run on <code>h</code>. That gap is the entire reason <code>HeapLocal</code> exists."
            },
            {
              "tac": "obtain ⟨hdEnd, r, hrex, hrst, hrhp⟩ := hlocal σ hP hR s' hd hex",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nh hP hR : Heap\nhd : hP.disjoint hR\nhu : h = hP.union hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ ∃ s', Exec c { store := σ, heap := h } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "The gap is closed: <code>hrex</code> is a run starting from <code>hP.union hR</code>. And <code>hdEnd : s'.heap.disjoint hR</code> is sitting there ready for the reassembly — the conjunct the textbook statement omits."
            },
            {
              "tac": "subst hu",
              "state": "P Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ ∃ s', Exec c { store := σ, heap := hP.union hR } s' ∧ (Q ∗ R) s'.store s'.heap",
              "h": "<code>h</code> is gone; the goal now starts from <code>hP.union hR</code>, matching <code>hrex</code> exactly. Do this <i>before</i> the <code>refine</code>."
            },
            {
              "tac": "refine ⟨r, hrex, s'.heap, hR, hdEnd, hrhp, ?_, ?_⟩",
              "state": "case refine_1\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ Q r.store s'.heap",
              "h": "First hole: <code>Q</code> at the new store but the old (small) heap. The context is exactly what it was before the <code>refine</code>; only the goal has changed, and it is now labelled <code>case refine_1</code>."
            },
            {
              "tac": "· rw [hrst]; exact hq",
              "state": "case refine_2\nP Q R : Assertion\nc : Cmd\nhc : Hoare P c Q\nhlocal : HeapLocal c\nhpres : Preserves c R\nσ : Store\nhP hR : Heap\nhd : hP.disjoint hR\nhp : P σ hP\nhr : R σ hR\ns' : State\nhex : Exec c { store := σ, heap := hP } s'\nhq : Q s'.store s'.heap\nhdEnd : s'.heap.disjoint hR\nr : State\nhrex : Exec c { store := σ, heap := hP.union hR } r\nhrst : r.store = s'.store\nhrhp : r.heap = s'.heap.union hR\n⊢ R r.store hR",
              "h": "Second hole: <code>R</code> at the new store and the untouched frame heap. There is no way to prove this from <code>hr : R σ hR</code> alone — the store changed. This is the goal <code>Preserves</code> was invented for."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "steps",
          "title": "The eight components of the final refine",
          "items": [
            {
              "k": "<code>r</code>",
              "h": "The witness for <code>∃ s'</code> in the unfolded <code>Hoare</code>: the big run’s final state."
            },
            {
              "k": "<code>hrex</code>",
              "h": "The execution <code>Exec c ⟨σ, hP.union hR⟩ r</code>, straight from locality."
            },
            {
              "k": "<code>s'.heap</code>, <code>hR</code>",
              "h": "The witnesses for <code>∃ h₁ h₂</code> in the unfolded <code>Q ∗ R</code>. This is the cut, and it is the only decision in the proof."
            },
            {
              "k": "<code>hdEnd</code>",
              "h": "Their disjointness. Available only because <code>HeapLocal</code> carries it."
            },
            {
              "k": "<code>hrhp</code>",
              "h": "<code>r.heap = s'.heap.union hR</code>: the union equation of the star. The locality conclusion is stated in exactly this form so that no massaging is needed here."
            },
            {
              "k": "<code>?_</code>, <code>?_</code>",
              "h": "<code>Q</code> of the first piece and <code>R</code> of the second, both at the new store. The first is bookkeeping; the second is the <code>Preserves</code> obligation."
            }
          ]
        },
        {
          "t": "detail",
          "title": "What this proof does <i>not</i> use",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "No induction on <code>c</code>. No case analysis on <code>Exec</code>. No lemma about <code>∗</code> from M4 — not associativity, not commutativity, not the unit laws. No determinism of <code>Exec</code>. No finiteness of heaps."
            },
            {
              "t": "p",
              "h": "That is worth pausing on. The frame rule is not a fact about the particular commands in this language; it is a fact about any relation satisfying <code>HeapLocal</code>. The command-specific work all happens in the four exercises above, and it is completely separated from this proof. Add a new command tomorrow, prove <code>HeapLocal</code> for it, and the frame rule extends for free."
            }
          ]
        }
      ],
      "pitfall": "Forgetting <code>subst hu</code>, or doing the <code>refine</code> first and hoping to fix it later. The goal keeps saying <code>Exec c { store := σ, heap := h } r</code> while <code>hrex</code> says <code>Exec c { store := σ, heap := hP.union hR } r</code>, and Lean reports an <i>application</i> type mismatch inside <code>And.intro</code>, which is a confusing place to be told about it:<br><code>Application type mismatch: The argument hrex has type Exec c { store := σ, heap := hP.union hR } r but is expected to have type Exec c { store := σ, heap := h } r</code>. <code>h</code> and <code>hP.union hR</code> are propositionally equal, not definitionally, so nothing will close that gap except rewriting — and <code>subst</code> is the cheapest rewrite.",
      "variants": "Drop <code>hpres</code> and the second hole is unprovable — see the counterexample earlier in the chapter, where <code>x := 1</code> refutes the framed triple with an empty heap. Drop <code>hlocal</code> and you cannot even get started: <code>hc</code> gives an execution on <code>hP</code> and there is no route from that to an execution on <code>h</code>; a Hoare triple says nothing about bigger heaps. Weaken <code>hlocal</code> by removing its disjointness conjunct and the fifth component of the <code>refine</code> has nothing to fill it. Finally, note that the proof never uses <code>hd : hP.disjoint hR</code> directly — it only passes it to <code>hlocal</code>. All of the initial-disjointness reasoning has been pushed into the locality lemmas, which is exactly the modularity you were buying."
    },
    {
      "t": "ex",
      "id": "m8-6",
      "name": "write_with_frame",
      "hard": false,
      "why": "The reason we did all of that. Do <b>not</b> prove this by unfolding two cells. The point of the exercise is that the proof does not grow when the frame does: replace <code>other ↦ w</code> by a ten-thousand-node linked list and not one character changes.",
      "setup": "In scope: <code>hoare_write l e old : Hoare (l ↦ old) (.write l e) (fun σ h => (l ↦ (e.eval σ)) σ h)</code> from M7, plus this chapter’s <code>hoare_frame</code>, <code>heapLocal_write</code>, <code>preserves_of_heapOnly</code> and <code>heapOnly_pointsTo</code>.",
      "goal": "theorem write_with_frame (l other : Loc) (old new w : Val) :\n    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new))\n      ((l ↦ new) ∗ (other ↦ w))",
      "hints": [
        "Do not <code>intro</code> anything. This is an application of <code>hoare_frame</code> and nothing else; if you find yourself looking at a heap, you have taken a wrong turn.",
        "<code>hoare_frame</code> needs three arguments: the small triple, a locality proof, and a <code>Preserves</code> proof. The small triple is <code>hoare_write l (.const new) old</code>; naming it with a <code>have</code> that ascribes the postcondition <code>l ↦ new</code> makes the application easier to read, though inlining it also works.",
        "The <code>Preserves</code> argument is <code>preserves_of_heapOnly _ (heapOnly_pointsTo other w)</code>. The underscore is the command, which <code>preserves_of_heapOnly</code> takes explicitly and <i>first</i> — omit it and Lean complains that a <code>Prop</code> was supplied where a <code>Cmd</code> was expected."
      ],
      "sol": "theorem write_with_frame (l other : Loc) (old new w : Val) :\n    Hoare ((l ↦ old) ∗ (other ↦ w)) (.write l (.const new)) ((l ↦ new) ∗ (other ↦ w)) := by\n  have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=\n    hoare_write l (.const new) old\n  exact hoare_frame base (heapLocal_write l (.const new))\n    (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
      "expl": "Five lines, and none of them mentions a heap. Now imagine the frame is a linked list of ten thousand nodes: the proof does not change at all. That invariance is the entire practical argument for separation logic.",
      "walk": [
        {
          "tac": "have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) :=",
          "h": "Names the small triple with the postcondition written the way you want to read it. <code>hoare_write</code>’s postcondition is the store-dependent <code>fun σ h => (l ↦ (e.eval σ)) σ h</code>; ascribing the type <code>l ↦ new</code> asks Lean to check that <code>(Atom.const new).eval σ</code> reduces to <code>new</code>, which it does definitionally, so the ascription goes through. This step is for the reader — inlining the term into the <code>exact</code> below also compiles."
        },
        {
          "tac": "hoare_write l (.const new) old",
          "h": "The M7 rule, instantiated. Nothing else is needed for the footprint: the write owns exactly one cell."
        },
        {
          "tac": "exact hoare_frame base (heapLocal_write l (.const new))",
          "h": "Applies the frame rule with <code>P := l ↦ old</code>, <code>Q := l ↦ new</code>, <code>R := other ↦ w</code>. All three are inferred from the goal; the locality argument is the exercise you proved above, instantiated at this command."
        },
        {
          "tac": "(preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
          "h": "The store-stability obligation. <code>other ↦ w</code> ignores its store argument, so <code>heapOnly_pointsTo</code> applies and <code>preserves_of_heapOnly</code> converts it. The <code>_</code> is the command, recovered by unification."
        }
      ],
      "deep": [
        {
          "t": "trace",
          "title": "write_with_frame, tactic by tactic",
          "start": "l other : Loc\nold new w : Val\n⊢ Hoare (l ↦ old ∗ other ↦ w) (Cmd.write l (Atom.const new)) (l ↦ new ∗ other ↦ w)",
          "steps": [
            {
              "tac": "have base : Hoare (l ↦ old) (.write l (.const new)) (l ↦ new) := hoare_write l (.const new) old",
              "state": "l other : Loc\nold new w : Val\nbase : Hoare (l ↦ old) (Cmd.write l (Atom.const new)) (l ↦ new)\n⊢ Hoare (l ↦ old ∗ other ↦ w) (Cmd.write l (Atom.const new)) (l ↦ new ∗ other ↦ w)",
              "h": "One new hypothesis. Note what the goal looks like: <code>Hoare (l ↦ old ∗ other ↦ w) … (l ↦ new ∗ other ↦ w)</code> — no heaps, no unions, no disjointness anywhere on the screen."
            },
            {
              "tac": "exact hoare_frame base (heapLocal_write l (.const new)) (preserves_of_heapOnly _ (heapOnly_pointsTo other w))",
              "state": "No goals.",
              "h": "Three arguments, three obligations, done. Unification reads <code>P</code>, <code>Q</code> and <code>R</code> off the goal."
            }
          ],
          "done": "No goals."
        },
        {
          "t": "cmp",
          "left": {
            "t": "Without the frame rule (M7 style)",
            "kind": "bad",
            "h": "You would <code>intro σ h hstar</code>, destructure the star into <code>Heap.singleton l old</code> and <code>Heap.singleton other w</code>, build the union, prove the cell exists in it with <code>union_of_some</code>, construct the <code>Exec.write</code> derivation, then prove <code>Heap.write (union …) l new = Heap.union (Heap.singleton l new) (Heap.singleton other w)</code> by <code>funext</code> and a three-way case split. Roughly twenty lines. Now do it for three cells."
          },
          "right": {
            "t": "With the frame rule",
            "kind": "good",
            "h": "Four lines, and the length is <i>independent of the frame</i>. That independence is the entire practical argument for separation logic; everything else in this chapter was the price of admission."
          }
        },
        {
          "t": "detail",
          "title": "Where does <code>l ≠ other</code> come from?",
          "tag": "aside",
          "open": false,
          "blocks": [
            {
              "t": "p",
              "h": "It is never stated and never needed as a hypothesis, because it is <i>implied</i> by the precondition. <code>(l ↦ old) ∗ (other ↦ w)</code> asserts a split of the heap into two disjoint singletons, and M4’s <code>two_cells_distinct</code> extracts <code>l ≠ other</code> from exactly that. If <code>l = other</code>, the precondition is simply unsatisfiable and the triple holds vacuously."
            },
            {
              "t": "p",
              "h": "This is one of the quiet wins of the <code>∗</code> notation: the non-aliasing side conditions that clutter a classical Hoare-logic development are absorbed into the connective, and the frame rule inherits them without ever mentioning them."
            }
          ]
        }
      ],
      "pitfall": "Writing <code>preserves_of_heapOnly (heapOnly_pointsTo other w)</code> without the leading <code>_</code>. The command is an explicit argument of <code>preserves_of_heapOnly</code> and it comes <i>first</i>, so this passes a <code>HeapOnly</code> proof where a <code>Cmd</code> is expected:<br><code>Application type mismatch: The argument heapOnly_pointsTo other w has type HeapOnly (other ↦ w) of sort `Prop` but is expected to have type Cmd of sort `Type` in the application preserves_of_heapOnly (heapOnly_pointsTo other w)</code>. Reading that quickly, it is easy to conclude something is wrong with <code>heapOnly_pointsTo</code>; nothing is — you are one underscore short. The other way to lose time here is to start with <code>intro σ h hstar</code> out of habit. Nothing in this proof needs a heap in scope, and once you have unfolded <code>Hoare</code> you cannot apply <code>hoare_frame</code> to the goal any more without folding it back up.",
      "variants": "Frame something store-dependent instead — say <code>pure (fun σ => σ x = 3)</code> — and <code>heapOnly_pointsTo</code> is no help, because <code>pure</code> reads the store. For a <code>write</code> you are still fine, but via a different route: M9’s <code>preserves_of_storeStable (storeStable_write l e) _</code>, which observes that a write does not touch the store at all and therefore preserves <i>every</i> assertion. Frame the same thing around a <code>.assign x</code> and it genuinely fails — that is the counterexample from the start of this chapter. Take <code>other := l</code> and the theorem remains true but becomes vacuous: <code>(l ↦ old) ∗ (l ↦ w)</code> is unsatisfiable, so there is nothing to prove."
    },
    {
      "t": "h3",
      "s": "What is left, and what is not"
    },
    {
      "t": "p",
      "h": "You have <code>HeapLocal</code> for <code>skip</code>, <code>assign</code>, <code>load</code>, <code>write</code>, <code>free</code> and <code>;;</code>. Two commands are not in the exercises. The conditional is the same argument twice and is here as a free sample; the loop needs induction on the execution derivation, and is worth doing once, below."
    },
    {
      "t": "code",
      "tag": "illustration",
      "src": "theorem heapLocal_ite {b : BExpr} {c₁ c₂ : Cmd}\n    (h₁ : HeapLocal c₁) (h₂ : HeapLocal c₂) : HeapLocal (.ite b c₁ c₂) := by\n  intro σ h hFrame s' hd hex\n  cases hex with\n  | iteTrue hb hex =>\n      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₁ σ h hFrame s' hd hex\n      exact ⟨hdEnd, r, Exec.iteTrue hb hr, hst, hhp⟩\n  | iteFalse hb hex =>\n      obtain ⟨hdEnd, r, hr, hst, hhp⟩ := h₂ σ h hFrame s' hd hex\n      exact ⟨hdEnd, r, Exec.iteFalse hb hr, hst, hhp⟩",
      "cap": "not in the corpus — compiles against prelude/m8.lean"
    },
    {
      "t": "p",
      "h": "Both branches are a single <code>obtain</code> and a single <code>exact</code>, and the boolean side condition <code>hb</code> transfers unchanged because <code>b.eval</code> reads only the store. That is worth noticing: <b>the frame is invisible to the guard</b>, for the same reason it is invisible to a load."
    },
    {
      "t": "h4",
      "s": "The loop"
    },
    {
      "t": "p",
      "h": "Nothing in the workbook needs <code>HeapLocal (.loop b c)</code> — M13 verifies loops through <code>partialHoare_while</code> and an invariant, and never frames one. But it is true, and the way you have to set it up is a manoeuvre you will meet again in M13, so here it is in full."
    },
    {
      "t": "p",
      "h": "The obvious first move fails. <code>induction hex</code> on <code>hex : Exec (.loop b c) ⟨σ, h⟩ s'</code> gets:"
    },
    {
      "t": "state",
      "src": "error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)\n  Cmd.loop b c",
      "cap": "induction hex, straight off"
    },
    {
      "t": "p",
      "h": "To induct on a derivation, Lean needs every index of the inductive family to be a <i>variable</i>, so that the motive can be abstracted over it. The command index here is the concrete term <code>Cmd.loop b c</code>, not a variable. The standard repair — the same one M13 uses for <code>loop_invariant</code> — is to prove a statement about an arbitrary <code>cmd</code> and carry the equation <code>cmd = .loop b₀ c₀</code> as a hypothesis. The eight branches that cannot be a loop are then killed by <code>cases</code> on that equation, which sees a constructor clash and closes the goal outright."
    },
    {
      "t": "p",
      "h": "Two more things have to be generalised, and both for the same reason: the induction hypothesis is used at the <i>middle</i> state of one unrolling, so it must be available there. The start state becomes an arbitrary <code>s</code> rather than <code>⟨σ, h⟩</code>, and <code>hFrame</code> goes <i>after</i> the equation, so that the IH is quantified over frames rather than fixed to one."
    },
    {
      "t": "code",
      "tag": "illustration",
      "src": "theorem heapLocal_loop_aux {b₀ : BExpr} {c₀ : Cmd} (hc : HeapLocal c₀) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      ∀ hFrame, Heap.disjoint s.heap hFrame →\n        Heap.disjoint s'.heap hFrame ∧\n        ∃ r : State,\n          Exec (.loop b₀ c₀) ⟨s.store, Heap.union s.heap hFrame⟩ r ∧\n          r.store = s'.store ∧\n          r.heap = Heap.union s'.heap hFrame := by\n  intro cmd s s' hex\n  induction hex with\n  | skip => intro heq; cases heq\n  | assign => intro heq; cases heq\n  | load _ => intro heq; cases heq\n  | write _ => intro heq; cases heq\n  | free _ => intro heq; cases heq\n  | seq _ _ _ _ => intro heq; cases heq\n  | iteTrue _ _ _ => intro heq; cases heq\n  | iteFalse _ _ _ => intro heq; cases heq\n  | loopFalse hb =>\n      intro heq hFrame hd\n      cases heq\n      exact ⟨hd, _, Exec.loopFalse hb, rfl, rfl⟩\n  | loopTrue hb hbdy hrst _ ihrst =>\n      intro heq hFrame hd\n      cases heq\n      obtain ⟨hdMid, r₁, hr₁, hst₁, hhp₁⟩ := hc _ _ hFrame _ hd hbdy\n      obtain ⟨hdEnd, r₂, hr₂, hst₂, hhp₂⟩ := ihrst rfl hFrame hdMid\n      refine ⟨hdEnd, r₂, Exec.loopTrue hb hr₁ ?_, hst₂, hhp₂⟩\n      have heq : r₁ = ⟨r₁.store, r₁.heap⟩ := rfl\n      rw [hst₁, hhp₁] at heq\n      rw [heq]\n      exact hr₂\n\ntheorem heapLocal_loop {b : BExpr} {c : Cmd} (hc : HeapLocal c) :\n    HeapLocal (.loop b c) := by\n  intro σ h hFrame s' hd hex\n  exact heapLocal_loop_aux hc hex rfl hFrame hd",
      "cap": "not in the corpus — compiles against prelude/m8.lean"
    },
    {
      "t": "p",
      "h": "The <code>loopTrue</code> branch is <code>heapLocal_seq</code> with the tail supplied by the induction hypothesis instead of by a second assumption: body through <code>hc</code>, tail through <code>ihrst</code>, glued with <code>Exec.loopTrue</code>. The underscores in <code>hc _ _ hFrame _ hd hbdy</code> are the store, the heap and the middle state, all of which Lean reads off <code>hbdy</code> — necessary here because <code>induction</code> left those states inaccessible and you cannot type their names."
    },
    {
      "t": "p",
      "h": "That same inaccessibility forces a different spelling of the structure-eta step. In <code>heapLocal_seq</code> you could write <code>have heq : r₁ = ⟨sMid.store, …⟩</code> because <code>sMid</code> had a name. Here you cannot, so you start from the one equation you can always state — <code>r₁ = ⟨r₁.store, r₁.heap⟩</code>, true by <code>rfl</code> — and then rewrite <i>forwards</i> with <code>hst₁</code> and <code>hhp₁</code> to push it into the shape the goal wants. Same fact, obtained from the other end."
    },
    {
      "t": "note",
      "h": "Do <b>not</b> add a command “allocate exactly location <code>l</code>” and keep an unrestricted frame rule. If the frame already owns <code>l</code>, the allocation is not local and the rule becomes unsound. The three honest fixes are: a side condition that the frame does not own <code>l</code>; nondeterministic fresh allocation with an existential in the postcondition; or moving to finite heaps so that a fresh location provably exists.",
      "title": "Allocation breaks locality if you are careless",
      "kind": "warn"
    },
    {
      "t": "p",
      "h": "M9 puts this to work. Two glue lemmas there — <code>preserves_of_storeStable</code> and <code>hoare_write_val</code> — make the <code>Preserves</code> obligation and the store-dependent postcondition disappear in practice, and after that every verification is <code>hoare_seq</code>, <code>hoare_frame</code>, a small rule, and <code>hoare_consequence</code> to reshape the assertion. If <code>Exec</code> appears in one of your proofs from now on, you are missing a lemma."
    },
    {
      "t": "dod",
      "h": "You have proved the frame rule from operational locality rather than accepting it as an axiom, and you know exactly which properties of the language it depends on."
    }
  ]
});
