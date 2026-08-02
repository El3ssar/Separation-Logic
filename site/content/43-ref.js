registerChapter({
  id: 'ref',
  num: '§',
  phase: 'Reference',
  title: 'Notation, theorems, discipline',
  blurb: 'Every symbol with the keystrokes that produce it and the definition it abbreviates; all 239 theorems with the unit that proves them; and five rules about how to lay a proof out.',

  /* Every number on this page was counted, not remembered:
       239 theorems   grep '^theorem' over site/lean/e2/*.lean
       319 decls, 2327 lines   tools/e2/verify.sh 43
       112 `simp`     tokens, comments stripped, `simpa` excluded
     The theorem-index table was generated from the fragments and pasted, so a
     new theorem in a fragment needs a new name in the row for its unit.

     The unit cell is the same deep link § `tactics` uses: `data-go` is the
     file's position in ledger.json's `order`, which is the file prefix and the
     order integrate.mjs emits the <script> tags in.

     No ledgerAllow. This is the last file in the course, so every name it uses
     is at or above its own row, and it names no banned tactic. */

  orient: {
    youWill: [
      'Type any symbol the course uses, recognise the two messages that mean you typed the wrong star, and know which one glyph you have to copy rather than type.',
      'Unfold <code>↦</code>, <code>∗</code>, <code>-∗</code>, <code>⊢</code>, <code>pure</code>, <code>Hoare</code> or <code>wp</code> to the definition it abbreviates, and check the unfolding with <code>rfl</code>.',
      'Drop brackets safely, because you know the four precedences and which way each connective associates.',
      'Find any of the 239 theorems by the unit that proves it, or by the shape of the goal you are stuck on.',
      'Lay out a development so that the algebra can be reused when the model changes — five rules, each of them a mistake this course would otherwise have made.'
    ],
    needs: [
      'Nothing. Every entry names the unit that owes you the explanation.'
    ],
    payoff: 'You look a thing up instead of reconstructing it.'
  },

  blocks: [

    /* ------------------------------------------------------------ framing --- */

    {t:'p', h:'§ <code>tactics</code> sent you here for the other half, and this is not a unit either. That page lists what you type at a goal. This one lists what you read: the symbols and what each abbreviates, every theorem the course proves and where, and five rules about the shape of a development. Nothing here introduces a tactic, a notation or a name you have not already met, and no section depends on any other — find the row you came for and stop.'},

    {t:'p', h:'The counts are counts. There are 239 theorems in the verified corpus and 319 declarations in 2327 lines; the corpus calls <code>simp</code> 112 times, and the section on proof discipline says where. The theorem index was generated from the Lean fragments rather than transcribed, so every name in it is a name Lean has accepted.'},

    /* --------------------------------------------------------- notation ---- */

    {t:'sec', s:'Notation'},

    {t:'p', h:'A symbol you cannot type is a symbol you cannot use, so keystrokes come first. In the editor on these pages, type the backslash form and press space or tab; the glyph replaces it. A palette of the commonest glyphs sits above it for a keyboard that will not produce them, and it does not carry everything in the table below. Where several spellings give the same glyph, any of them works.'},

    {t:'tbl', cap:'The abbreviations the editor on these pages accepts, in the order you meet them.',
     head:['type this', 'and you get', 'what it is', 'introduced'],
     rows:[
       ['<code>\\to</code>, <code>\\r</code>', '<code>→</code>', 'the function type, and implication', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="0">00 · <code>aliasing</code></button>'],
       ['<code>\\not</code>', '<code>¬</code>', '<code>¬ P</code> is <code>P → False</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="0">00 · <code>aliasing</code></button>'],
       ['<code>\\ne</code>', '<code>≠</code>', 'disequality; <code>simp</code> is what turns it into <code>¬ a = b</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="0">00 · <code>aliasing</code></button>'],
       ['<code>\\and</code>', '<code>∧</code>', 'conjunction of propositions', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="0">00 · <code>aliasing</code></button>'],
       ['<code>\\&lt;</code>, <code>\\&gt;</code>', '<code>⟨ ⟩</code>', 'the pattern that takes a pair apart, and from Unit 01 the constructor that builds one', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="0">00 · <code>aliasing</code></button>'],
       ['<code>\\1</code>, <code>\\2</code>', '<code>₁ ₂</code>', 'subscripts, which are part of a name and not decoration', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="0">00 · <code>aliasing</code></button>'],
       ['<code>\\or</code>, <code>\\iff</code>', '<code>∨ ↔</code>', 'the other two propositional connectives', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="2">01 · <code>terms</code></button>'],
       ['<code>\\forall</code>, <code>\\exists</code>', '<code>∀ ∃</code>', 'the quantifiers', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="2">01 · <code>terms</code></button>'],
       ['<code>\\cdot</code>', '<code>·</code>', 'the focus dot: one bullet per goal', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="2">01 · <code>terms</code></button>'],
       ['<code>\\l</code>', '<code>←</code>', 'inside <code>rw [← h]</code>: run the equation right to left', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="3">02 · <code>compute</code></button>'],
       ['<code>\\sigma</code>', '<code>σ</code>', 'the store, in every assertion proof in the course', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>\\vdash</code>', '<code>⊢</code>', 'entailment between assertions — and the turnstile in front of every goal', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<i>no abbreviation</i>', '<code>⊣⊢</code>', 'entailment both ways; see the warning below', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>\\mapsto</code>', '<code>↦</code>', 'ownership of exactly one cell', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="15">13 · <code>pointsto</code></button>'],
       ['<code>\\star</code>, <code>\\ast</code>, <code>\\sep</code>', '<code>∗</code>', 'separating conjunction', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="16">14 · <code>star</code></button>'],
       ['<code>;;</code>', '<code>;;</code>', 'sequencing, and two ASCII semicolons is all it is', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="21">18 · <code>language</code></button>'],
       ['<code>\\triangle</code>', '<code>▸</code>', 'rewriting inside a term with an equation', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="23">20 · <code>induction</code></button>'],
       ['<code>\\wand</code>, <code>\\magic</code>', '<code>-∗</code>', 'the magic wand: an ASCII hyphen and the same U+2217 as <code>∗</code>, so <code>-*</code> will not do','<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="37">34 · <code>wand</code></button>']
     ]},

    {t:'note', kind:'warn', title:'Two you cannot type',
     h:'<code>⊣⊢</code> has no abbreviation in the editor on these pages and is not on the palette. It costs you nothing while you are doing the exercises, because the statement is filled in for you and only the proof is yours — but if you are writing a statement of your own, as the design exercises ask, copy the glyph out of the table above. <code>✝</code> is different: Lean prints it on names it invented, and it is unwritable on purpose. <code>rename_i</code> is how you get such a hypothesis back.'},

    {t:'p', h:'Now the brackets. Four precedences are in play, and tighter binds first: <code>↦</code> at 60 and <code>;;</code> at 60, <code>∗</code> at 55, <code>-∗</code> at 54, then <code>⊢</code> and <code>⊣⊢</code> at 40. <code>∗</code>, <code>-∗</code> and <code>;;</code> all associate to the right, so an unbracketed chain of any of them is right-nested. That last fact is why Unit 16 has to prove associativity at all: <code>(P ∗ Q) ∗ R</code> is a different term from what <code>P ∗ Q ∗ R</code> parses as.'},

    {t:'code', tag:'illustration', cap:'Each is closed by <code>rfl</code>: after parsing, the two sides are one term rather than two equivalent ones. When you are unsure how an expression brackets, this is a two-line way to ask Lean instead of guessing.',
     src:'-- ↦ at 60, ∗ at 55, -∗ at 54, ⊢ and ⊣⊢ at 40: tighter binds first.\nexample (l₁ l₂ : Loc) (v₁ v₂ : Val) (R : Assertion) :\n    (l₁ ↦ v₁ ∗ l₂ ↦ v₂ -∗ R) = (((l₁ ↦ v₁) ∗ (l₂ ↦ v₂)) -∗ R) := rfl\n\n-- ∗ and -∗ are right-associative, so an unbracketed chain is right-nested.\nexample (P Q R : Assertion) : (P ∗ Q ∗ R) = (P ∗ (Q ∗ R)) := rfl\nexample (P Q R : Assertion) : (P -∗ Q -∗ R) = (P -∗ (Q -∗ R)) := rfl\n\n-- ;; is right-associative at 60.\nexample (c₁ c₂ c₃ : Cmd) : (c₁ ;; c₂ ;; c₃) = (c₁ ;; (c₂ ;; c₃)) := rfl'},

    {t:'p', h:'The trap is on the other side of <code>⊢</code>. At 40 it binds tighter than <code>∧</code>, which sits at 35, so <code>P ⊢ Q ∧ R</code> parses as <code>(P ⊢ Q) ∧ R</code> — and since <code>R</code> is an <code>Assertion</code> rather than a <code>Prop</code>, the conjunction is ill-typed. Assertion-level conjunction is <code>aAnd</code>, and this is the message you get for forgetting it.'},

    {t:'state', cap:'From <code>example (P Q R : Assertion) : P ⊢ Q ∧ R</code>, with the line-and-column prefix dropped. Lean redisplays the whole application, which makes the message look like a complaint about the term you wrote; the information is in the two types.',
     src:'error: Application type mismatch: The argument\n  R\nhas type\n  Assertion\nbut is expected to have type\n  Prop\nin the application\n  P ⊢ Q ∧ R'},

    {t:'p', h:'The other two notation errors both come from a star that is not <code>∗</code>. Unicode has several star-shaped operators and the notation is declared for exactly one of them, U+2217 <span style="font-variant:small-caps">asterisk operator</span>. Paste in U+22C6 <span style="font-variant:small-caps">star operator</span>, <code>⋆</code>, which is a pixel or two different on most fonts, and Lean has no notation for it, so it stops at the character with no name to report. Type an ASCII <code>*</code> and something worse happens: that spelling <i>is</i> notation, for multiplication, and Lean goes looking for a way to multiply two assertions.'},

    {t:'state', cap:'Two separate compilations: above, <code>P ⋆ Q ⊢ Q ⋆ P</code>; below, <code>P * Q ⊢ Q * P</code>. Line prefixes dropped, along with the standing <code>Hint</code> about <code>trace.Meta.synthInstance</code> and a second copy of the same message for the second <code>*</code>. Two glyphs away from the same statement, two unrelated failures.',
     src:'error: expected token\n\nerror(lean.synthInstanceFailed): failed to synthesize instance of type class\n  HMul Assertion Assertion ?m.3'},

    /* ----------------------------------------------------- what it means --- */

    {t:'sec', s:'What each symbol stands for'},

    {t:'p', h:'Notation hides a definition, which is what makes it worth having and also what makes a goal stop meaning anything. When that happens the fix is almost always to unfold one row of this table by hand. The third column is the whole definition, not a paraphrase: every assertion in the course is a predicate on a store and a heap, and the notation is a way of not writing that out.'},

    {t:'tbl', cap:'The notations, the assertions they are built from, and the judgements about programs, in the order the course builds them. The rest of the vocabulary — the list predicates, the locality predicates, the programs themselves — is in the inventory further down.',
     head:['written', 'Lean name', 'what it literally is', 'introduced'],
     rows:[
       ['<code>P σ h</code>', '<code>Assertion</code>', '<code>Store → Heap → Prop</code> — an assertion is a predicate on a state', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>P ⊢ Q</code>', '<code>Entails</code>', '<code>∀ σ h, P σ h → Q σ h</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>P ⊣⊢ Q</code>', '<code>AssertionEquiv</code>', '<code>Entails P Q ∧ Entails Q P</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>aAnd P Q</code>, <code>aOr P Q</code>', '<code>aAnd</code>, <code>aOr</code>', '<code>fun σ h =&gt; P σ h ∧ Q σ h</code>, and the same with <code>∨</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>aExists P</code>', '<code>aExists</code>', '<code>fun σ h =&gt; ∃ x, P x σ h</code>, with <code>x</code> of any <code>Sort u</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>fact φ</code>', '<code>fact</code>', '<code>fun σ _ =&gt; φ σ</code> — true of the store, silent about the heap', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="14">12 · <code>assertions</code></button>'],
       ['<code>emp</code>', '<code>emp</code>', '<code>fun _ h =&gt; h = Heap.empty</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="15">13 · <code>pointsto</code></button>'],
       ['<code>l ↦ v</code>', '<code>pointsTo</code>', '<code>fun _ h =&gt; h = Heap.singleton l v</code> — the heap <i>is</i> that cell', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="15">13 · <code>pointsto</code></button>'],
       ['<code>P ∗ Q</code>', '<code>star</code>', '<code>fun σ h =&gt; ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="16">14 · <code>star</code></button>'],
       ['<code>aForall P</code>', '<code>aForall</code>', '<code>fun σ h =&gt; ∀ x, P x σ h</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="17">15 · <code>star-algebra</code></button>'],
       ['<code>pure φ</code>', '<code>pure</code>', '<code>aAnd (fact φ) emp</code> — <code>φ</code> holds and I own nothing', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="19">17 · <code>pure</code></button>'],
       ['<code>c₁ ;; c₂</code>', '<code>Cmd.seq</code>', 'a constructor of <code>Cmd</code>, under an infix', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="21">18 · <code>language</code></button>'],
       ['<code>Hoare P c Q</code>', '<code>Hoare</code>', '<code>∀ σ h, P σ h → ∃ s\', Exec c ⟨σ, h⟩ s\' ∧ Q s\'.store s\'.heap</code> — safety is the existential', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="25">22 · <code>hoare</code></button>'],
       ['<code>PartialHoare P c Q</code>', '<code>PartialHoare</code>', '<code>∀ σ h s\', P σ h → Exec c ⟨σ, h⟩ s\' → Q s\'.store s\'.heap</code> — no existential, so no safety claim', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="25">22 · <code>hoare</code></button>'],
       ['<code>subst x e Q</code>', '<code>subst</code>', '<code>fun σ h =&gt; Q (Store.set σ x (e.eval σ)) h</code> — substitution done in the model', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="25">22 · <code>hoare</code></button>'],
       ['<code>wp c Q</code>', '<code>wp</code>', '<code>fun σ h =&gt; ∃ s\', Exec c ⟨σ, h⟩ s\' ∧ Q s\'.store s\'.heap</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="34">31 · <code>wp</code></button>'],
       ['<code>P -∗ Q</code>', '<code>wand</code>', '<code>fun σ h =&gt; ∀ h\', Heap.disjoint h h\' → P σ h\' → Q σ (Heap.union h h\')</code>', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="37">34 · <code>wand</code></button>'],
       ['<code>bTrue b</code>, <code>bFalse b</code>', '<code>bTrue</code>, <code>bFalse</code>', '<code>fun σ _ =&gt; b.eval σ = true</code>, and <code>= false</code> — a guard as an assertion', '<button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="38">35 · <code>partial</code></button>']
     ]},

    {t:'p', h:'A table of definitions can be wrong in a way a table of theorems cannot, so eight of these rows were put to Lean. Each line below is an equation between a row&rsquo;s left column and its third, closed by <code>rfl</code> — the strongest form the claim can take, since it says the two sides are the same term rather than provably equal ones.'},

    {t:'code', tag:'illustration', cap:'Compiled against the finished course. If any of these eight had been paraphrased in the table above rather than quoted, the corresponding line here would fail.',
     src:'example (l : Loc) (v : Val) : (l ↦ v) = fun _ h => h = Heap.singleton l v := rfl\nexample : emp = fun _ h => h = Heap.empty := rfl\nexample (φ : Store → Prop) : pure φ = aAnd (fact φ) emp := rfl\nexample (P Q : Assertion) : (P ⊢ Q) = ∀ σ h, P σ h → Q σ h := rfl\nexample (P Q : Assertion) : (P ⊣⊢ Q) = ((P ⊢ Q) ∧ (Q ⊢ P)) := rfl\nexample (P Q : Assertion) :\n    (P ∗ Q) = fun σ h => ∃ h₁ h₂, Heap.disjoint h₁ h₂ ∧ h = Heap.union h₁ h₂ ∧ P σ h₁ ∧ Q σ h₂ := rfl\nexample (P Q : Assertion) :\n    (P -∗ Q) = fun σ h => ∀ h\', Heap.disjoint h h\' → P σ h\' → Q σ (Heap.union h h\') := rfl\nexample (P Q : Assertion) (c : Cmd) : Hoare P c Q = (P ⊢ wp c Q) := rfl'},

    {t:'p', h:'The last line is the one worth staring at. Unfold <code>Hoare P c Q</code> and unfold <code>P ⊢ wp c Q</code> and you arrive at the same string of symbols, which is why Unit 31 can prove <code>hoare_iff_entails_wp</code> with <code>Iff.rfl</code> and no argument at all. Two notations, one definition.'},

    /* ---------------------------------------------------- theorem index ---- */

    {t:'sec', s:'The theorem index'},

    {t:'p', h:'Two hundred and thirty-nine theorems, by the unit that proves them. Every one is in the verified corpus, which compiles as a single file under Lean 4.32.2 with no imports, no Mathlib and no <code>sorry</code>. The names are systematic on purpose — the prefix is the object (<code>heap</code>, <code>union</code>, <code>disjoint</code>, <code>splits</code>, <code>star</code>, <code>wand</code>, <code>hoare</code>, <code>heapLocal</code>, <code>wp</code>, <code>listRep</code>, <code>lseg</code>, <code>partialHoare</code>) and the suffix is the shape, so guessing a name is a reasonable first move.'},

    {t:'tbl', cap:'Generated from the Lean fragments. Two units are missing from it because they prove their statements as unnamed <code>example</code>s: Unit 00, whose two are the first proofs in the course, and Unit 07, whose three exhibit the two readings of ownership and are meant to be discarded once the choice is made.',
     head:['unit', 'n', 'theorems'],
     rows:[
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"2\">01 · <code>terms</code></button>", "13", "<code>implication_example</code>, <code>exists_example</code>, <code>exists_three</code>, <code>two_add_two</code>, <code>mp</code>, <code>comp</code>, <code>and_comm'</code>, <code>or_comm'</code>, <code>and_comm_tac</code>, <code>or_comm_tac</code>, <code>exists_mono</code>, <code>nested_pack</code>, <code>nested_unpack</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"3\">02 · <code>compute</code></button>", "10", "<code>rw_demo</code>, <code>calc_demo</code>, <code>double'_unfold</code>, <code>double'_three</code>, <code>double_unfold</code>, <code>double_zero_left</code>, <code>some_inj</code>, <code>some_ne_none</code>, <code>some_ne_none'</code>, <code>defined_of_ne_none</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"4\">03 · <code>funext</code></button>", "6", "<code>function_extensionality</code>, <code>twice_succ</code>, <code>apply_eq</code>, <code>funext_drill</code>, <code>if_drill</code>, <code>by_cases_drill</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"5\">04 · <code>update</code></button>", "5", "<code>update_same</code>, <code>update_other</code>, <code>update_shadow</code>, <code>update_comm</code>, <code>update_idem</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"7\">05 · <code>heap</code></button>", "6", "<code>singleton_same</code>, <code>singleton_other</code>, <code>write_same</code>, <code>write_other</code>, <code>erase_same</code>, <code>erase_other</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"8\">06 · <code>heap-laws</code></button>", "12", "<code>heap_ext</code>, <code>write_shadow</code>, <code>erase_write_same</code>, <code>write_comm</code>, <code>write_singleton</code>, <code>erase_singleton</code>, <code>erase_erase</code>, <code>write_of_eq</code>, <code>erase_write_comm</code>, <code>write_erase_same</code>, <code>erase_comm</code>, <code>write_empty</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"10\">08 · <code>disjoint</code></button>", "6", "<code>disjoint_symm</code>, <code>disjoint_empty_left</code>, <code>disjoint_empty_right</code>, <code>singleton_disjoint</code>, <code>singleton_disjoint_iff</code>, <code>self_disjoint_iff_empty</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"11\">09 · <code>union</code></button>", "6", "<code>union_of_none</code>, <code>union_of_some</code>, <code>union_eq_none</code>, <code>union_empty_left</code>, <code>union_empty_right</code>, <code>union_self</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"12\">10 · <code>pcm</code></button>", "5", "<code>union_assoc</code>, <code>union_comm</code>, <code>disjoint_union_left</code>, <code>disjoint_union_right</code>, <code>union_cancel_left</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"13\">11 · <code>splits</code></button>", "5", "<code>splits_empty_right</code>, <code>splits_empty_left</code>, <code>splits_comm</code>, <code>splits_assoc</code>, <code>union_not_comm</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"14\">12 · <code>assertions</code></button>", "13", "<code>entails_refl</code>, <code>entails_trans</code>, <code>and_left</code>, <code>and_right</code>, <code>and_intro</code>, <code>or_left</code>, <code>or_right</code>, <code>or_elim</code>, <code>equiv_refl</code>, <code>equiv_symm</code>, <code>equiv_trans</code>, <code>and_comm_iff</code>, <code>and_assoc_iff</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"15\">13 · <code>pointsto</code></button>", "3", "<code>pointsTo_value_unique</code>, <code>pointsTo_not_emp</code>, <code>emp_iff_all_none</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"16\">14 · <code>star</code></button>", "6", "<code>star_intro</code>, <code>star_same_loc_absurd</code>, <code>star_pointsTo_same_false</code>, <code>no_star_weakening</code>, <code>no_star_duplication</code>, <code>starNoDisj_dup</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"17\">15 · <code>star-algebra</code></button>", "17", "<code>star_emp_left</code>, <code>star_emp_right</code>, <code>star_emp_left_intro</code>, <code>star_emp_right_intro</code>, <code>star_comm</code>, <code>star_mono</code>, <code>star_mono_left</code>, <code>star_mono_right</code>, <code>star_or_left</code>, <code>star_exists_left</code>, <code>star_forall_left</code>, <code>star_forall_right_fails</code>, <code>star_emp_left_iff</code>, <code>star_emp_right_iff</code>, <code>star_comm_iff</code>, <code>star_congr</code>, <code>star_not_weakening</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"18\">16 · <code>star-assoc</code></button>", "3", "<code>star_assoc_left</code>, <code>star_assoc_right</code>, <code>star_assoc_iff</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"19\">17 · <code>pure</code></button>", "8", "<code>two_cells_distinct</code>, <code>star_swap_middle</code>, <code>star_rotate_left</code>, <code>star_rotate_right</code>, <code>star_pure_left</code>, <code>star_pure_right</code>, <code>star_or_right</code>, <code>star_exists_right</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"21\">18 · <code>language</code></button>", "2", "<code>storeSet_same</code>, <code>storeSet_other</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"22\">19 · <code>exec</code></button>", "5", "<code>exec_skip_inv</code>, <code>exec_assign_inv</code>, <code>exec_load_inv</code>, <code>exec_load_stuck</code>, <code>exec_skip_seq_inv</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"23\">20 · <code>induction</code></button>", "4", "<code>allZeros_length</code>, <code>append_nil</code>, <code>exec_id</code>, <code>exec_deterministic</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"24\">21 · <code>interpreter</code></button>", "6", "<code>run_sound</code>, <code>run_mono</code>, <code>run_le</code>, <code>run_complete</code>, <code>run_spin_none</code>, <code>spin_diverges</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"25\">22 · <code>hoare</code></button>", "6", "<code>hoare_consequence</code>, <code>hoare_skip</code>, <code>hoare_seq</code>, <code>hoare_assign</code>, <code>assign_constant</code>, <code>assign_twice</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"26\">23 · <code>small-footprint</code></button>", "6", "<code>hoare_load</code>, <code>hoare_write</code>, <code>hoare_free</code>, <code>clearCell_spec</code>, <code>writeTwice_spec</code>, <code>readAndFree_spec</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"27\">24 · <code>locality</code></button>", "9", "<code>preserves_of_heapOnly</code>, <code>heapOnly_pointsTo</code>, <code>heapOnly_emp</code>, <code>heapOnly_star</code>, <code>heapLocal_skip</code>, <code>heapLocal_assign</code>, <code>heapLocal_load</code>, <code>not_heapOnly_pure</code>, <code>frame_needs_preserves</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"28\">25 · <code>local-heap</code></button>", "3", "<code>write_union_no_disjointness</code>, <code>heapLocal_write</code>, <code>heapLocal_free</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"29\">26 · <code>local-compose</code></button>", "4", "<code>heapLocal_seq</code>, <code>heapLocal_ite</code>, <code>heapLocal_loop_aux</code>, <code>heapLocal_loop</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"30\">27 · <code>frame</code></button>", "3", "<code>hoare_frame</code>, <code>write_with_frame</code>, <code>free_with_frame</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"31\">28 · <code>aliasing-closed</code></button>", "2", "<code>classical_conjunction_rule_is_false</code>, <code>separated_write_ok</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"32\">29 · <code>symbolic</code></button>", "12", "<code>storeStable_write</code>, <code>storeStable_free</code>, <code>preserves_of_storeStable</code>, <code>readAndFree_framed</code>, <code>hoare_write_val</code>, <code>pure_star_regroup</code>, <code>hoare_load_and</code>, <code>and_fact_star</code>, <code>and_fact_star_intro</code>, <code>copyCell_spec</code>, <code>exec_seq_assoc</code>, <code>moveCell_spec</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"33\">30 · <code>swap</code></button>", "3", "<code>preserves_load_fact</code>, <code>swap_heap</code>, <code>swap_spec</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"34\">31 · <code>wp</code></button>", "11", "<code>hoare_iff_entails_wp</code>, <code>wp_skip</code>, <code>wp_assign</code>, <code>wp_seq</code>, <code>wp_mono</code>, <code>wp_sound</code>, <code>wp_weakest</code>, <code>heap_eq_singleton</code>, <code>wp_free_emp</code>, <code>wp_write</code>, <code>wp_frame</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"35\">32 · <code>listrep</code></button>", "6", "<code>listRep_nil</code>, <code>listRep_cons_unfold</code>, <code>listRep_cons_fold</code>, <code>listRep_cons_ne_zero</code>, <code>node_cells_distinct</code>, <code>concrete_list</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"36\">33 · <code>lseg</code></button>", "5", "<code>aExists_mono</code>, <code>lseg_nil_iff</code>, <code>lseg_append</code>, <code>lseg_listRep</code>, <code>listRep_null</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"37\">34 · <code>wand</code></button>", "11", "<code>wand_intro</code>, <code>wand_elim</code>, <code>star_wand_adjunction</code>, <code>wand_mono</code>, <code>wand_unit</code>, <code>hole_intro</code>, <code>hole_elim</code>, <code>wand_curry</code>, <code>wand_uncurry</code>, <code>emp_wand_elim</code>, <code>emp_wand_intro</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"38\">35 · <code>partial</code></button>", "7", "<code>partial_of_total</code>, <code>partialHoare_skip</code>, <code>partialHoare_seq</code>, <code>partialHoare_consequence</code>, <code>partialHoare_ite</code>, <code>hoare_ite</code>, <code>wp_ite</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"39\">36 · <code>invariant</code></button>", "3", "<code>loop_invariant</code>, <code>partialHoare_while</code>, <code>countdown_keeps_cell</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"40\">37 · <code>variant</code></button>", "5", "<code>hoare_while_variant</code>, <code>countdown_spec</code>, <code>drain_step</code>, <code>drain_stop</code>, <code>drain_spec</code>"],
       ["<button style=\"all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px\" data-go=\"41\">38 · <code>beyond</code></button>", "2", "<code>pcmStar_comm</code>, <code>pcmStar_unit_left</code>"]
     ]},

    /* --------------------------------------------------- by goal shape ----- */

    {t:'sec', s:'Finding it by the shape of the goal'},

    {t:'p', h:'Remembering two hundred names is not the skill; indexing them by what the goal looks like is. Almost every stuck goal in this course is one of the twenty-one shapes below, and for each of them the answer is a small named set rather than a search.'},

    {t:'tbl', cap:'The left column is what is on your screen. Where a row gives several names they are alternatives or a family, not a sequence.',
     head:['your goal looks like', 'reach for', 'from'],
     rows:[
       ['two heaps are equal', '<code>funext</code> on the location, then <code>by_cases</code>, then <code>simp</code> with the definitions; <code>heap_ext</code> is the first of those steps under a name', '06'],
       ['<code>Heap.union h₁ h₂ l = …</code> at one location', '<code>union_of_none</code>, <code>union_of_some</code>, <code>union_eq_none</code>', '09'],
       ['disjointness of a union, either side', '<code>disjoint_union_left</code>, <code>disjoint_union_right</code> — both are <code>↔</code>, so usable in either direction', '10'],
       ['two singletons disjoint', '<code>singleton_disjoint</code>, <code>singleton_disjoint_iff</code>', '08'],
       ['a heap in three pieces, bracketed the wrong way', '<code>splits_assoc</code>, <code>union_assoc</code>', '10, 11'],
       ['chaining entailments', '<code>entails_refl</code>, <code>entails_trans</code>; <code>equiv_trans</code> for a chain of <code>⊣⊢</code>', '12'],
       ['re-bracketing or re-ordering a chain of <code>∗</code>', '<code>star_assoc_left</code>, <code>star_assoc_right</code>, <code>star_swap_middle</code>, <code>star_rotate_left</code>, <code>star_rotate_right</code>', '16, 17'],
       ['an <code>emp</code> to add or to remove', '<code>star_emp_left</code>, <code>star_emp_right</code>, their two <code>_intro</code> converses, and the <code>_iff</code> forms for rewriting', '15'],
       ['one side of a <code>∗</code> to improve, the other to leave alone', '<code>star_mono</code>, <code>star_mono_left</code>, <code>star_mono_right</code>', '15'],
       ['a <code>pure</code> or a <code>fact</code> stuck inside a <code>∗</code>', '<code>star_pure_left</code>, <code>star_pure_right</code>, <code>pure_star_regroup</code>, <code>and_fact_star</code>', '17, 29'],
       ['you need <code>l₁ ≠ l₂</code> and hold no hypothesis saying so', '<code>two_cells_distinct</code> — separation <i>proves</i> non-aliasing', '17'],
       ['a precondition too strong, or a postcondition too weak', '<code>hoare_consequence</code>', '22'],
       ['a <code>;;</code> to split, and an intermediate assertion to choose', '<code>hoare_seq</code>', '22'],
       ['one cell of many, and a rule that mentions one', '<code>hoare_frame</code>, plus a <code>heapLocal_*</code> and a <code>Preserves</code> proof', '27'],
       ['a <code>Preserves</code> obligation', '<code>preserves_of_heapOnly</code> for a frame that ignores the store, <code>preserves_of_storeStable</code> for a command that never writes to it', '24, 29'],
       ['a conditional', '<code>hoare_ite</code>, <code>partialHoare_ite</code>; <code>heapLocal_ite</code> for the locality half', '26, 35'],
       ['a linked list to unfold or to fold back up', '<code>listRep_cons_unfold</code>, <code>listRep_cons_fold</code>, <code>listRep_null</code>', '32, 33'],
       ['two list segments to join', '<code>lseg_append</code>, <code>lseg_listRep</code>', '33'],
       ['moving an assumption across a <code>∗</code>', '<code>wand_intro</code>, <code>wand_elim</code>, <code>star_wand_adjunction</code>', '34'],
       ['working backwards from a postcondition', '<code>hoare_iff_entails_wp</code>, then <code>wp_seq</code>, <code>wp_mono</code>, <code>wp_skip</code>, <code>wp_assign</code>, <code>wp_frame</code>', '31'],
       ['a loop', '<code>partialHoare_while</code> for partial correctness, <code>hoare_while_variant</code> for total', '36, 37']
     ]},

    /* ------------------------------------------------------- discipline ---- */

    {t:'sec', s:'Proof discipline'},

    {t:'p', h:'Five rules about the shape of a development rather than the content of a proof. None of them is a matter of taste: each names a mistake this course was in a position to make, and there is a place in the corpus where you can see what not making it bought.'},

    {t:'ol', items:[
      '<b>Prove the semantic lemmas before you introduce the notation.</b> Notation hides a definition, which is worth doing only once you no longer need to see it.',
      '<b>Keep primitive specifications small.</b> A write rule mentions one cell. If yours mentions two you have baked a frame into it, and it will not compose.',
      '<b>Keep the resource algebra apart from the program semantics.</b> A law of <code>∗</code> must not mention commands, and a Hoare-rule proof must not do pointwise reasoning about heaps. When you catch yourself writing <code>funext</code> inside a triple, stop and extract a lemma.',
      '<b>Automate last.</b> A <code>simp</code> that closes a goal about disjoint union teaches you nothing about disjoint union. Reach for it after the manual proof, not instead of it.',
      '<b>Draw the decomposition before writing any Lean.</b> Most of the hard proofs here are bookkeeping about a heap in three pieces. Two minutes with a pen saves twenty in the editor.'
    ]},

    {t:'steps', title:'Where each rule was earned',
     items:[
       {k:'1 · Semantics before notation', h:'<p>Units 06 and 10 prove <code>write_shadow</code>, <code>union_assoc</code> and <code>disjoint_union_left</code> before <code>↦</code> exists at Unit 13 or <code>∗</code> at Unit 14, and that ordering is why the algebra of <code>∗</code> is so short. <code>star_comm</code> is two tactics. <code>star_mono</code> is two. <code>star_assoc_left</code>, the longest of the laws, is six, and all it does is apply <code>disjoint_union_left.mp</code>, <code>disjoint_union_right.mpr</code> and <code>union_assoc</code> and put six slots back in a different order. Had <code>∗</code> come first, every one of those proofs would have unfolded to an argument about heaps, and <code>union_assoc</code> would have been proved four times inline with slightly different phrasing each time.</p>'},
       {k:'2 · Small primitives', h:'<p><code>hoare_write</code> mentions exactly one cell. The two-cell version is not a primitive but a two-tactic derivation: <code>write_with_frame</code> names <code>hoare_write l (.const new) old</code> as <code>base</code> and hands it to <code>hoare_frame</code> with <code>heapLocal_write</code> and <code>preserves_of_heapOnly _ (heapOnly_pointsTo other w)</code>. Had the two-cell rule been primitive you would need a three-cell version, and one for a second cell that is a list, and so on without end. The frame rule exists so that the list of primitives is one item long.</p>'},
       {k:'3 · Algebra apart from semantics', h:'<p>Not one of the six theorems in Unit 23 contains a <code>funext</code>. Every heap-level fact they need — <code>singleton_same</code>, <code>write_singleton</code>, <code>erase_singleton</code>, <code>disjoint_empty_left</code>, <code>union_empty_left</code> — arrives as a named lemma from Units 05, 06, 08 and 09. That is what makes Unit 38&rsquo;s second project tractable: the semantics changes in one place and the heap algebra is untouched, because the two were never entangled. Check that claim rather than trusting it — it is the cheapest test of whether a development is layered.</p>'},
       {k:'4 · Automation last', h:'<p>The corpus calls <code>simp</code> 112 times, and where those calls sit is the argument. Thirty-two of them — nearly a third — are in Unit 21, the optional interpreter, grinding the fuel-indexed <code>run</code> against <code>Exec</code>; that is bookkeeping with no separation-logic content in it. Units 13 to 17, which build <code>↦</code> and the whole algebra of <code>∗</code>, contain thirteen between them, and every single one is a <code>(by simp)</code> settling a numeric disequality inside a concrete counterexample, or a <code>simp [Heap.empty]</code>. Not one law of <code>∗</code> — commutativity, associativity, the unit laws, monotonicity — uses <code>simp</code> at all. Seven of the last eight units contain none, and Unit 37&rsquo;s five are arithmetic on a loop counter.</p>'},
       {k:'5 · Draw it first', h:'<p><code>splits_assoc</code>, <code>star_assoc_left</code>, <code>lseg_append</code> and <code>hoare_frame</code> are four of the hardest proofs here, and all four are the same kind of bookkeeping: a heap cut into named pieces and put back in a different arrangement — three pieces re-bracketed in the first three, and in <code>hoare_frame</code> two pieces of which the command replaces one. Drawing it is not a metaphor: <code>lseg_append</code>&rsquo;s <code>cons</code> case is seven entailment steps and not one of them mentions a heap — <code>star_mono_left</code>, then <code>star_exists_left</code> and <code>aExists_mono</code> to move the existential out of the way, then <code>star_assoc_left</code> and <code>star_mono_right</code> twice, down to the induction hypothesis. Once the picture is on paper the Lean is a transcription; without it you are doing the re-bracketing and the tactic search at the same time, and it is the tactic search that will fail.</p>'}
     ]},

    {t:'note', kind:'warn', title:'The one that is hardest to keep',
     h:'Rule 4. Once a <code>simp</code> call has closed a goal you will not go back and find out why, and the day it stops closing one you have nothing to work with. <code>simp [Heap.write, hne]</code> proves <code>Heap.write h l v x = h x</code> when <code>hne : x ≠ l</code>, and leaves <code>⊢ x = l → some v = h x</code> when the hypothesis is <code>hne : l ≠ x</code> — <code>simp</code> turned the first into the rewrite <code>(x = l) = False</code> and could make no use of the second. The fix is <code>hne.symm</code>, and it is invisible unless you already know that a disequality remembers which side is which. § <code>errors</code> makes that point twice, for <code>rw</code> and for a lemma argument, and nowhere for <code>simp</code>. Automation you do not understand is not leverage. It is a proof you cannot repair.'},

    /* ---------------------------------------------------- what was built --- */

    {t:'sec', s:'What you built'},

    {t:'p', h:'A separation logic from an empty file: a heap and its partial commutative monoid; assertions, entailment and <code>∗</code> with its laws; a small imperative language with a relational semantics and an executable one proved to agree; safe Hoare triples; load, write and free rules that mention one cell each; locality, and the frame rule as a theorem about it; verified copy, move and swap programs; recursive list and list-segment predicates with the theorem that joins two segments; the magic wand and its adjunction; weakest preconditions; and loop rules for partial and for total correctness.'},

    {t:'p', h:'The theorem index above is what was proved; this is what was defined. The two lists together are the whole corpus: 319 named declarations, 239 of them theorems and the 80 below, plus twelve further statements proved as unnamed <code>example</code>s.'},

    {t:'dl', items:[
      {k:'The model', h:'<code>Loc</code>, <code>Val</code>, <code>Heap</code>, <code>Var</code>, <code>Store</code> (Unit 00); <code>Assertion</code> (12); <code>State</code> (18)'},
      {k:'Heap operations', h:'<code>Heap.empty</code>, <code>Heap.singleton</code>, <code>Heap.write</code>, <code>Heap.erase</code> (05); <code>Heap.disjoint</code>, <code>Heap.union</code>, <code>Heap.splits</code> (08)'},
      {k:'Resource algebra', h:'<code>PCM</code>, <code>heapPCM</code> (10); <code>pcmStar</code> (38)'},
      {k:'Assertions', h:'<code>Entails</code>, <code>AssertionEquiv</code>, <code>aTrue</code>, <code>aFalse</code>, <code>aAnd</code>, <code>aOr</code>, <code>aExists</code>, <code>fact</code> (12); <code>emp</code>, <code>pointsTo</code> (13); <code>star</code>, <code>starNoDisj</code> (14); <code>aForall</code> (15); <code>pure</code> (17); <code>wand</code> (34)'},
      {k:'The language', h:'<code>Atom</code>, <code>Atom.eval</code>, <code>Atom.size</code>, <code>Store.set</code>, <code>BExpr</code>, <code>BExpr.eval</code>, <code>Cmd</code> (18); <code>Exec</code> (19); <code>run</code> (21)'},
      {k:'The program logic', h:'<code>Hoare</code>, <code>PartialHoare</code>, <code>subst</code> (22); <code>wp</code> (31); <code>bTrue</code>, <code>bFalse</code> (35)'},
      {k:'Locality', h:'<code>HeapLocalWeak</code>, <code>HeapLocal</code>, <code>Preserves</code>, <code>HeapOnly</code> (24); <code>StoreStable</code> (29)'},
      {k:'Structures in the heap', h:'<code>node</code>, <code>listRep</code> (32); <code>lseg</code> (33)'},
      {k:'Programs, with specifications', h:'<code>clearCell</code>, <code>readAndFree</code> (23); <code>copyCell</code>, <code>moveCell</code> (29); <code>swap</code> (30); <code>counterGuard</code>, <code>countdown</code> (36); <code>drainBody</code>, <code>drain</code>, <code>drainInv</code> (37)'},
      {k:'Warm-ups and exhibits', h:'<code>aliasedAfter</code>, <code>twoAllocated</code> (00); <code>double</code>, <code>double\'</code>, <code>defined</code> (02); <code>twice</code> (03); <code>update</code> (04); <code>ptsAtLeast</code>, <code>ptsExactly</code>, <code>twoCells</code> (07); <code>Pcx</code> (15); <code>allZeros</code> (20); <code>demoProg</code>, <code>demoStart</code>, <code>spin</code> (21). <code>update</code> is not a warm-up: it is the store&rsquo;s operation, defined fourteen units before the language that needs it, and Unit 18 closes <code>@Store.set = @update</code> with <code>rfl</code>.'}
    ]},

    {t:'quote', h:'That is a small but genuine separation logic, rather than a collection of Hoare-logic examples.'},

    /* ---------------------------------------------------------- onwards --- */

    {t:'sec', s:'What comes next'},

    {t:'p', h:'The seven ideas worth keeping, and three projects, close <button style="all:unset;cursor:pointer;text-decoration:underline;text-underline-offset:2px" data-go="41">38 · <code>beyond</code></button>, where they were argued rather than listed. The projects are allocation, address expressions, and the two linked-list capstones; each carries a scope estimate and the theorems it obliges you to revisit, and each is a project rather than an exercise because nobody in this course has a verified solution to it. If you want a fourth, take rule 3 at its word and swap the carrier: instantiate <code>PCM</code> with fractional permissions or with a multiset of tokens, and see how much of Module 3 comes with you.'},

    {t:'dod', h:'You can produce every symbol the course uses — all but one of them from the keyboard — and recognise the two errors that mean you typed the wrong star. You can unfold any of them to the definition underneath, a predicate on a store and a heap wherever it is an assertion, and check the unfolding with <code>rfl</code>. Given an unfamiliar goal you can say within seconds whether it is a heap equality, an entailment or a triple, and name the family of lemmas that settles it. And you can say which of your proofs would survive replacing the heap with a different resource, because you know which of them ever looked at what a heap is.'}

  ]
});
