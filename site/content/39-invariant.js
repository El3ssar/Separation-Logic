registerChapter({
  id: 'invariant',
  num: '36',
  phase: 'Phase 8 · Control and termination',
  ledgerForward: ['hoare_while_variant', 'countdown_spec'],
  title: 'The invariant rule',
  blurb: 'One theorem — the loop rule — and the manoeuvre it needs: induct on a derivation whose command is fixed, by making it a variable and adding an equation that pins it back.',

  orient: {
    youWill: [
      'State the invariant rule, and defend both guard conjuncts by deriving the two weaker rules that drop them.',
      'Prove the <code>loopFalse</code> branch by <code>cases</code> alone, and say exactly which branch <code>cases</code> cannot close and why.',
      'Read <code>Invalid target: Index in target\'s type is not a variable</code> off two more proofs, and name the offending index in each: the command, and then the state <code>intro σ h</code> built.',
      'Strengthen a statement by quantifying its indices and adding an equation, and refute the version that quantifies without adding one.',
      'Kill eight branches of a ten-branch induction with one line each, and say what makes the line work.',
      'Read the two induction hypotheses of the <code>loopTrue</code> branch, say which is dead, and say why the rule\'s premise is exactly the fact the dead one would have supplied.',
      'Apply the rule to a concrete loop whose invariant is an ownership claim the body never touches, and unpack what the postcondition tells you when it stops.'
    ],
    needs: [
      'Unit 19: <code>Exec</code>, its ten rules, and the two that conclude a <code>loop</code> run.',
      'Unit 20: <code>induction</code> over a derivation, and <code>cases</code> on an equation between two constructors.',
      'Unit 26: the constant-command induction idiom, and the refusal that forces it.',
      'Unit 35: <code>PartialHoare</code>, its five binders, and <code>bTrue</code> / <code>bFalse</code>.'
    ],
    payoff: 'Everything after this page assumes you can find an invariant. Unit 37 adds the second half — a quantity that decreases — and the two together turn a partial triple about a loop into a total one. The technique underneath, generalise-then-constrain, is not about loops at all: it is what you do to any statement about a derivation whose index is pinned.'
  },

  blocks: [

    /* ================================================== picking up the thread ==== */

    {t:'p', h:"Generalise, then constrain. The fix costs one helper theorem whose statement looks nothing like the rule it proves, so before building it, write the rule down. Deciding what a loop rule should say is half of proving it."},

    {t:'p', h:"A loop has no fixed number of steps, so nothing true of it can be a claim about a fixed number of steps. What can be claimed instead is that some assertion survives one turn. Call it <code>I</code>. Suppose <code>I</code> holds when the loop is entered, and suppose one run of the body — entered with <code>I</code> holding <i>and</i> the guard true — leaves <code>I</code> holding. Then <code>I</code> holds after any number of turns, including none. And when the loop stops, it stops for a reason: the guard evaluated to <code>false</code>. An assertion with that property is a <b>loop invariant</b>."},

    {t:'svg', cap:'A run of a loop, drawn as Unit 19 draws it: one <code>loopTrue</code> storey per iteration, a <code>loopFalse</code> on top. The invariant is checked at every landing. The premise of the rule is one storey; the conclusion is the whole building, of a height the picture cannot fix.',
     src:"<svg viewBox=\"0 0 640 250\" role=\"img\" aria-label=\"A vertical stack of four states. The bottom state is labelled I, the guard is true, and an arrow labelled body leads to the next state, also labelled I. This repeats. At the top the guard is false and the run stops, with the top state labelled I and not b.\">\n  <defs>\n    <marker id=\"ah39\" viewBox=\"0 0 10 10\" refX=\"9\" refY=\"5\" markerWidth=\"7\" markerHeight=\"7\" orient=\"auto-start-reverse\">\n      <path d=\"M 0 0 L 10 5 L 0 10 z\" fill=\"currentColor\"/>\n    </marker>\n  </defs>\n  <g class=\"dg\">\n    <text x=\"16\" y=\"228\" class=\"dg-note\">entry</text>\n    <rect class=\"dg-box a\" x=\"96\" y=\"206\" width=\"64\" height=\"30\" rx=\"5\"/>\n    <text x=\"128\" y=\"226\" text-anchor=\"middle\" class=\"dg-t\">I</text>\n    <path d=\"M 168 221 L 256 221\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah39)\"/>\n    <text x=\"212\" y=\"212\" text-anchor=\"middle\" class=\"dg-note\">body</text>\n    <text x=\"330\" y=\"226\" class=\"dg-note\">guard true, so the body runs</text>\n\n    <rect class=\"dg-box a\" x=\"96\" y=\"146\" width=\"64\" height=\"30\" rx=\"5\"/>\n    <text x=\"128\" y=\"166\" text-anchor=\"middle\" class=\"dg-t\">I</text>\n    <path d=\"M 168 161 L 256 161\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" marker-end=\"url(#ah39)\"/>\n    <text x=\"212\" y=\"152\" text-anchor=\"middle\" class=\"dg-note\">body</text>\n    <text x=\"330\" y=\"166\" class=\"dg-note\">guard true, so the body runs</text>\n\n    <rect class=\"dg-box a\" x=\"96\" y=\"86\" width=\"64\" height=\"30\" rx=\"5\"/>\n    <text x=\"128\" y=\"106\" text-anchor=\"middle\" class=\"dg-t\">I</text>\n    <path d=\"M 128 82 L 128 62\" fill=\"none\" stroke=\"currentColor\" stroke-width=\"1.4\" stroke-dasharray=\"4 4\" opacity=\"0.7\"/>\n    <text x=\"330\" y=\"106\" class=\"dg-note\">⋯ some number of turns ⋯</text>\n\n    <rect class=\"dg-box b\" x=\"88\" y=\"22\" width=\"104\" height=\"30\" rx=\"5\"/>\n    <text x=\"140\" y=\"42\" text-anchor=\"middle\" class=\"dg-t\">I ∧ ¬b</text>\n    <text x=\"330\" y=\"42\" class=\"dg-note\">guard false, so the run ends here</text>\n    <text x=\"16\" y=\"42\" class=\"dg-note\">exit</text>\n  </g>\n</svg>"},

    {t:'p', h:"<b>The body's precondition carries the guard.</b> A body only ever runs at a state where the guard was true, so a proof about the body may assume it. Asking instead for <code>PartialHoare I c I</code> — the body preserves <code>I</code> whatever the guard did — gives a rule that is still correct and that you can much less often apply. A loop body is normally correct only under its guard; that is what the guard is for. A rule that declines to hand the guard over is asking for a body that would have been safe to run unconditionally, and a body like that did not need a loop."},

    {t:'p', h:"<b>The postcondition carries the negated guard.</b> The exit is where the information is. A loop stops because its guard went false, and that is a fact about the final store which nothing else in the proof will tell you. Drop the conjunct and the rule reports, after the loop, exactly what you knew before it."},

    {t:'p', h:"Each of those weakenings follows from the rule and the rule follows from neither, so the two conjuncts are not decoration: they are the difference between one theorem you can specialise and two you cannot strengthen. The derivations are compiled below, once the rule exists to derive them from."},

    {t:'p', h:"Which reading the rule is stated in was settled in Unit 35. A total triple obliges you to produce a run, and producing a run of a loop means producing a tower whose height nothing in <code>.loop b c</code> determines. The one premise available says what a single turn preserves and says nothing about how many turns there are, so there is nothing in it out of which such a tower could be built. The partial reading obliges you to nothing of the kind: a run is handed over and you say where it lands. So this rule is stated partially — and the same statement in the total reading is not a harder theorem, it is a false one. Unit 37 is about what has to be added."},

    {t:'anat', tag:'verified',
     src:"theorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by",
     parts:[
       {m:'{I : Assertion}', h:"The invariant is a parameter of the rule, not something the rule computes. Finding it is the reader's job, every time, and there is no procedure for it — which is why the rest of this page is one theorem and the next unit is a lab."},
       {m:'aAnd I (bTrue b)', h:"The body's precondition: the invariant, and the guard as an assertion. <code>aAnd</code> rather than <code>∗</code>, for the reason Unit 35 gave — a guard reads the store, owns no memory, and the body runs on the whole heap the loop was entered with."},
       {m:'PartialHoare I (.loop b c) (aAnd I (bFalse b))', h:"The conclusion. Precondition: the invariant alone. Postcondition: the invariant again, and the guard false. <code>I</code> occurs four times across the two lines and the caller supplies it once. Choosing it is the whole of using this rule; everything else in the statement is determined by the command."}
     ]},

    /* ================================================== cases, and where it stops ==== */

    {t:'sec', s:'Two branches, and one of them is the theorem again'},

    {t:'p', h:"Start it the way every partial rule starts. Five <code>intro</code>s put a run of <code>.loop b c</code> in your hands, and exactly two rules of <code>Exec</code> conclude such a run, so <code>cases hex</code> splits into two branches. That is the opening that proved the conditional rule."},

    {t:'code', tag:'sketch', cap:'The first branch closes. The second is left open, and the <code>sorry</code> is the whole subject of this page.',
     src:"theorem whileByCases {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by\n  intro σ h s' hI hex\n  cases hex with\n  | loopFalse hb => exact ⟨hI, hb⟩\n  | loopTrue hb hbdy hrest => sorry"},

    {t:'p', h:"<code>Exec.loopFalse</code> concludes <code>Exec (.loop b c) s s</code>: the loop is entered, the guard is false, and the final state is the initial one. So the invariant you were handed at the start is the invariant at the end, and the guard premise the constructor carries is the second conjunct. <code>⟨hI, hb⟩</code> takes one component from the caller and one from the derivation, and there is no work between them. The other branch is the one where the loop has run at least once."},

    {t:'state', cap:'The <code>loopTrue</code> branch, trimmed to <code>hI</code> and what the inversion produced; the seven omitted lines are the statement\'s own binders and <code>s\'</code>, unchanged. Every goal display on this page is <code>check.sh</code> output with the <code>snippet:line:col:</code> prefix dropped.',
     src:"case loopTrue\nhI : I σ h\ns'✝ : State\nhb : BExpr.eval { store := σ, heap := h }.store b = true\nhbdy : Exec c { store := σ, heap := h } s'✝\nhrest : Exec (Cmd.loop b c) s'✝ s'\n⊢ aAnd I (bFalse b) s'.store s'.heap"},

    {t:'p', h:"<code>hbdy</code> is a run of the body, and <code>hbody</code> is waiting to consume it. <code>hrest</code> is the difficulty: a run of <code>.loop b c</code> again, starting from the state the body reached, and what has to be known about it is the statement currently being proved. <code>cases</code> will not supply that. Splitting a derivation into its immediate premises is the whole of what it does; it never returns the conclusion at a smaller derivation. The tactic that does is <code>induction</code>."},

    /* ================================================== the refusal ==== */

    {t:'p', h:"So write <code>induction</code> instead, and the tactic refuses before either branch is reached."},

    {t:'code', tag:'sketch', cap:'Neither branch is elaborated. The error is on the <code>induction</code> line itself.',
     src:"theorem whileDirect {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by\n  intro σ h s' hI hex\n  induction hex with\n  | loopFalse hb => sorry\n  | loopTrue hb hbdy hrest ih1 ih2 => sorry"},

    {t:'state', cap:'The refusal, and the offending index printed underneath it.',
     src:"error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)\n  Cmd.loop b c"},

    {t:'p', h:"<code>Exec</code> has three indices — the command and the two states — and <code>induction</code> wants all three variable. The first one here is <code>.loop b c</code>, a constructor applied to two arguments, so there is no family to run over. Unit 26 met this refusal proving locality of a loop, and answered it with the manoeuvre below; Unit 35 named it again over the spinning command whose divergence it could not prove, and left that as a debt. Here the theorem <i>is</i> the loop rule, so there is nothing to defer to and nothing to route round."},

    {t:'p', h:"The second index has the same defect and is easier to miss. After <code>intro σ h</code> the initial state is <code>{ store := σ, heap := h }</code> — also a constructor applied to arguments. Quantifying the command alone moves the complaint along by one."},

    {t:'code', tag:'sketch', cap:'The command is now a bound variable and the two states are not. Refused on the same line, for the same reason, about a different index.',
     src:"theorem cmdOnly {I : Assertion} {b₀ : BExpr} {c₀ : Cmd} (σ : Store) (h : Heap) (s' : State) :\n    ∀ {cmd : Cmd}, Exec cmd ⟨σ, h⟩ s' → cmd = .loop b₀ c₀ →\n      I σ h → I s'.store s'.heap ∧ b₀.eval s'.store = false := by\n  intro cmd hex\n  induction hex with\n  | loopFalse hb => sorry\n  | _ => sorry"},

    {t:'state', cap:'Same message, and the index named underneath it is now the state built by <code>intro σ h</code>.',
     src:"error: Invalid target: Index in target's type is not a variable (consider using the `cases` tactic instead)\n  { store := σ, heap := h }"},

    /* ================================================== the idiom ==== */

    {t:'sec', s:'Generalise, and constrain'},

    {t:'p', h:"The manoeuvre from Unit 26, applied to all three indices at once. It has three moves and the middle one is where the mathematics is."},

    {t:'steps', title:'Turning a statement about one command into one an induction accepts', items:[
      {k:'Make every index a variable', h:"The three arguments of <code>Exec</code> become bound variables of the statement: <code>∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → …</code>. Quantifying over a whole <code>State</code> rather than over a store and a heap is what keeps the second and third indices variables; <code>⟨σ, h⟩</code> would not be one."},
      {k:'Put back what that gave away', h:"The statement is now about every command and it is false — <code>skip</code> falsifies no guard. So add, as a premise of the conclusion, the fact you deleted: <code>cmd = .loop b₀ c₀</code>. It goes inside the statement being generalised — to the right of the derivation, under the same quantifiers — and that is the point: each branch will hold its own copy of it, with <code>cmd</code> replaced by the constructor that branch is about."},
      {k:'Leave the rest under the arrow', h:"The invariant at the starting state is a premise too, for a reason that only shows up in one branch. The induction hypothesis for the tail of a loop has to be applied at the <i>middle</i> state, so the statement being generalised must quantify the starting state and take the invariant there as an argument. Where <code>intro</code> stops is then a matter of what you want to see: stopping after the derivation leaves the equation and the invariant in the goal, so the <code>induction</code> line displays exactly what is about to be generalised."}
    ]},

    {t:'p', h:"Test the second move rather than believe it. Take the strengthened statement with the equation deleted, keep a body premise that is genuinely satisfiable, and the conclusion is refutable at <code>skip</code>."},

    {t:'code', tag:'illustration', cap:'A guard that is true at every store, a body premise that holds — <code>skip</code> preserves <code>aTrue</code> — and the unconstrained conclusion carried to <code>False</code> by one application at <code>skip</code>. Generalising without constraining does not weaken the theorem; it destroys it.',
     src:"def guardAlwaysTrue : BExpr := .not (.equals (.const 0) (.const 1))\n\nexample : PartialHoare (aAnd aTrue (bTrue guardAlwaysTrue)) .skip aTrue := by\n  intro σ h s' hp hex\n  cases hex\n  trivial\n\nexample\n    (hover : ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' →\n      aTrue s.store s.heap →\n        aTrue s'.store s'.heap ∧ guardAlwaysTrue.eval s'.store = false) : False := by\n  have h := hover (s := ⟨fun _ => 0, Heap.empty⟩) Exec.skip trivial\n  simp [guardAlwaysTrue, BExpr.eval, Atom.eval] at h"},

    {t:'p', h:"The helper, with all three moves in it. <code>b₀</code> and <code>c₀</code> carry the subscript for the reason Unit 26's did: the branches of the induction will produce guards and bodies of their own."},

    {t:'code', tag:'verified', cap:'The statement only. The conclusion is <code>aAnd I (bFalse b₀)</code> at <code>s\'</code> written out: the two are the same term, and <code>rfl</code> proves it. Writing it folded also compiles, and then every branch goal displays as <code>aAnd I (bFalse b₀) s✝.store s✝.heap</code>, which hides which conjunct each line of the proof is producing.',
     src:"theorem loop_invariant {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by"},

    /* ================================================== the ten branches ==== */

    {t:'sec', s:'Ten branches, eight of them impossible'},

    {t:'p', h:"<code>intro cmd s s' hex</code> and stop."},

    {t:'state', cap:'Four names taken, and the goal is a chain of two arrows. The derivation is a hypothesis; the equation and the invariant are not.',
     src:"I : Assertion\nb₀ : BExpr\nc₀ : Cmd\nhbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I\ncmd : Cmd\ns s' : State\nhex : Exec cmd s s'\n⊢ cmd = Cmd.loop b₀ c₀ → I s.store s.heap → I s'.store s'.heap ∧ BExpr.eval s'.store b₀ = false"},

    {t:'p', h:"<code>induction hex with</code> is now accepted, and produces ten branches, one per rule of <code>Exec</code>. Eight of them are about commands that are not loops."},

    {t:'state', cap:'The <code>skip</code> branch, trimmed to the state names and the goal; the five omitted lines are the statement\'s own binders and the now-inert <code>cmd</code>, unchanged in all ten branches.',
     src:"case skip\ns s' s✝ : State\n⊢ Cmd.skip = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false"},

    {t:'p', h:"The head of that goal is <code>Cmd.skip = Cmd.loop b₀ c₀</code>. Nothing has to be established in this branch beyond the observation that its hypothesis cannot hold: <code>intro heq</code> names the equation and <code>cases heq</code> closes the branch outright, on no-confusion between two distinct constructors. Unit 20 met that move on a single heap lookup and Unit 26 on eight branches of one induction. Here it is eight branches again, one line each, differing only in the constructor at the head."},

    {t:'state', cap:'<code>loopFalse</code>, the first of the two survivors, trimmed the same way.',
     src:"case loopFalse\ns s' s✝ : State\nb✝ : BExpr\nc✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = false\n⊢ Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false"},

    {t:'p', h:"Two guards are in scope now and they are not the same object. <code>b✝</code> is the guard the <i>derivation</i> is about; <code>b₀</code> is the guard the <i>theorem</i> is about; <code>hb</code> says the first went false and the goal asks about the second. <code>heq</code> is what ties them together, and here its two sides are headed by the same constructor, so <code>cases heq</code> does its other job: it identifies the arguments, and <code>hb</code> comes back as a statement about <code>b₀</code>."},

    {t:'state', cap:'<code>loopTrue</code>, premises and goal, with the two induction hypotheses held back for the display below. The three premises are: the guard went true, the body ran to a middle state, and the loop ran again from there.',
     src:"case loopTrue\ns s' s✝ s'✝ s''✝ : State\nb✝ : BExpr\nc✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nhbdy : Exec c✝ s✝ s'✝\nhrest✝ : Exec (Cmd.loop b✝ c✝) s'✝ s''✝\n⊢ Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false"},

    {t:'p', h:"Two of those premises are derivations, so <code>induction</code> attached an induction hypothesis to each."},

    {t:'state', cap:'The two induction hypotheses, extracted from the same display. Each is the statement of the theorem instantiated at one sub-derivation, equation and all.',
     src:"hbody_ih✝ : c✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s'✝.store s'✝.heap ∧ BExpr.eval s'✝.store b₀ = false\nihrest :\n  Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀ → I s'✝.store s'✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false"},

    {t:'p', h:"<code>hbody_ih✝</code> is dead, and the equation is what kills it. Using it means proving <code>c✝ = Cmd.loop b₀ c₀</code>, which after the branch's own <code>cases heq</code> reads <code>c₀ = Cmd.loop b₀ c₀</code> — an equation whose right-hand side properly contains its left, satisfied by no command at all."},

    {t:'state', cap:'What offering <code>rfl</code> to it reports, with the branch opened as <code>| loopTrue hb hbdy _ ihbody ihrest =></code> so that the hypothesis has a name to be called by. The metavariable in the first type is Lean never getting as far as choosing what <code>rfl</code> was to be an identity of.',
     src:"error: Application type mismatch: The argument\n  rfl\nhas type\n  ?m.303 = ?m.303\nbut is expected to have type\n  c₀ = Cmd.loop b₀ c₀\nin the application\n  ihbody rfl"},

    {t:'p', h:"That is not a flaw in the statement. The body's run is a run of <code>c₀</code>, and this induction knows nothing whatever about commands that are not the loop — by construction, since the equation is what confines it. So the fact the dead induction hypothesis would have given you has to arrive from outside, and it does: it is <code>hbody</code>, the premise of the rule. The premise and the dead hypothesis are the same missing fact, supplied by the caller instead of by the induction."},

    {t:'p', h:"<code>ihrest</code> is the live one, and it is the theorem for the rest of the loop. It takes two arguments. The first is the equation, which the branch's own <code>cases heq</code> turns into an identity. The second is the invariant at the <i>middle</i> state — and <code>hI</code>, when it arrives, is the invariant at the state before the body ran. The gap between those two states is exactly one run of the body, which is what the rule's premise is about."},

    {t:'detail', title:'The three branch displays, untrimmed', open:false, blocks:[
      {t:'p', h:"Each of the trimmed displays above drops whole lines and changes none. Here they are as Lean prints them, from <code>trace_state</code> placed at the head of the branch."},
      {t:'state', cap:'<code>loopFalse</code>, eleven lines.',
       src:"case loopFalse\nI : Assertion\nb₀ : BExpr\nc₀ : Cmd\nhbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I\ncmd : Cmd\ns s' s✝ : State\nb✝ : BExpr\nc✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = false\n⊢ Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false"},
      {t:'state', cap:'<code>loopTrue</code>, sixteen lines, premises and induction hypotheses together.',
       src:"case loopTrue\nI : Assertion\nb₀ : BExpr\nc₀ : Cmd\nhbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I\ncmd : Cmd\ns s' s✝ s'✝ s''✝ : State\nb✝ : BExpr\nc✝ : Cmd\nhb : BExpr.eval s✝.store b✝ = true\nhbdy : Exec c✝ s✝ s'✝\nhrest✝ : Exec (Cmd.loop b✝ c✝) s'✝ s''✝\nhbody_ih✝ : c✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s'✝.store s'✝.heap ∧ BExpr.eval s'✝.store b₀ = false\nihrest :\n  Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀ → I s'✝.store s'✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false\n⊢ Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀ → I s✝.store s✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false"},
      {t:'state', cap:'And the <code>loopTrue</code> branch of the <i>earlier</i> attempt, the one that used <code>cases hex</code>, in full. Compare its <code>hrest</code> with <code>ihrest</code> above: same run, and in one of them you also hold the statement about it.',
       src:"case loopTrue\nI : Assertion\nb : BExpr\nc : Cmd\nhbody : PartialHoare (aAnd I (bTrue b)) c I\nσ : Store\nh : Heap\ns' : State\nhI : I σ h\ns'✝ : State\nhb : BExpr.eval { store := σ, heap := h }.store b = true\nhbdy : Exec c { store := σ, heap := h } s'✝\nhrest : Exec (Cmd.loop b c) s'✝ s'\n⊢ aAnd I (bFalse b) s'.store s'.heap"}
    ]},

    /* ================================================== the exercise ==== */

    {t:'ex',
     id:'m13-3',
     name:'loop_invariant and partialHoare_while',
     hard: true,
     why:"The invariant rule — the last rule the partial logic is missing, and the only one whose conclusion covers a run of a height nothing in the statement fixes. What it teaches beyond the rule is the manoeuvre, and the manoeuvre transfers to every proof you will ever write about a derivation whose index is fixed — which is most of them, because a theorem worth stating is usually about a particular command. Unit 37 proves <code>hoare_while_variant</code>, the total loop rule, and does <i>not</i> reuse this technique: it inducts on a natural number instead, and the contrast is only visible if you have written this one.",
     setup:"Two theorems. The first is the helper, statement given; the second is the rule, which follows from it in two lines. You have <code>Exec</code>'s ten constructors, <code>bTrue</code> and <code>bFalse</code> from Unit 35, and nothing else — no heap lemma appears anywhere in either proof. The branch names for <code>induction hex with</code> are the ten constructor names, each followed by a name or an underscore for every premise the rule carries and every induction hypothesis it earns — <code>| load _ =></code>, <code>| seq _ _ _ _ =></code>, and so on. A list shorter than that is legal and leaves the surplus inaccessible; a longer one is an error.",
     goal:"theorem loop_invariant {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by\n  sorry\n\ntheorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by",
     hints:[
       "Unfolded, the helper says: for every command and every pair of states, if that command runs from the first to the second, and the command is <code>.loop b₀ c₀</code>, and <code>I</code> holds at the first state, then <code>I</code> holds at the second and the guard is false there. The equation and the invariant are premises of the conclusion, not hypotheses of the theorem: they sit to the right of the derivation, under two arrows, and the statement of the second theorem contains neither.",
       "Induct on the derivation. Eight of the ten rules conclude a run of a command that is not a loop, so in those branches the equation is between two distinct constructors and the branch is finished by that observation alone. Of the two that remain, one has no sub-run and hands you the false guard directly; the other hands you a run of the body, a run of the loop from the middle state, and the theorem for that second run.",
       "Four <code>intro</code>s, not six — stop at the derivation, and leave the two arrows in the goal. Then <code>induction hex with</code>, and per branch: <code>intro</code> the equation and <code>cases</code> it. In the surviving branches you also want the invariant introduced. The body's induction hypothesis is unusable; the rule's premise <code>hbody</code> is what replaces it, and the second theorem's proof discharges the equation with <code>rfl</code>.",
       "<code>intro cmd s s' hex</code> then <code>induction hex with</code>. Eight branches read <code>| skip => intro heq; cases heq</code> and its siblings. <code>| loopFalse hb =></code> takes <code>intro heq hI</code>, then <code>cases heq</code>, and leaves a two-slot conjunction whose components are both in scope. <code>| loopTrue hb hbdy _ _ ihrest =></code> takes five names — three premises then two induction hypotheses — of which you use the first, the second and the last. The second theorem opens <code>intro σ h s' hI hex</code> and closes on one line: the helper, applied to <code>hbody</code>, to <code>hex</code>, to a proof of the equation and to <code>hI</code>, in that order."
     ],
     sol:"theorem loop_invariant {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by\n  intro cmd s s' hex\n  induction hex with\n  | skip => intro heq; cases heq\n  | assign => intro heq; cases heq\n  | load _ => intro heq; cases heq\n  | write _ => intro heq; cases heq\n  | free _ => intro heq; cases heq\n  | seq _ _ _ _ => intro heq; cases heq\n  | iteTrue _ _ _ => intro heq; cases heq\n  | iteFalse _ _ _ => intro heq; cases heq\n  | loopFalse hb =>\n      intro heq hI\n      cases heq\n      exact ⟨hI, hb⟩\n  | loopTrue hb hbdy _ _ ihrest =>\n      intro heq hI\n      cases heq\n      exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)\n\ntheorem partialHoare_while {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) := by\n  intro σ h s' hI hex\n  exact loop_invariant hbody hex rfl hI",
     solNote:"Twenty tactic lines across the two theorems, and eight of them differ only in the constructor they name. If you climbed all four hints and are still stuck, open this and read the <code>loopTrue</code> branch first — the other nine are bookkeeping and it is the only one that argues anything.",
     expl:"The helper is proved by induction over the derivation, which is legal only because its three indices were made variables and the equation put back what that gave away. Eight branches die on the equation. <code>loopFalse</code> hands over the exit fact and the final state is the initial one, so the invariant needs no moving. <code>loopTrue</code> is the induction step: the body's run plus the rule's premise re-establish the invariant one state along, and the induction hypothesis carries it from there to the end. The rule itself is the helper applied at the one command it was constrained to, with <code>rfl</code> for the equation.",
     walk:[
       {tac:'intro cmd s s\' hex', h:"Four names for the three quantified variables and the derivation. The equation and the invariant are left in the goal, so that the next line displays what it is about to generalise over. Taking them here as well compiles — <code>induction</code> reverts them itself — and the fold in the panel below shows that proof and what it costs."},
       {tac:'induction hex with', h:"Accepted, because all three of <code>Exec</code>'s indices are now variables. It replaces the goal by ten, one per rule, each with the indices instantiated to what that rule concludes — which is why every branch's equation has a different left-hand side."},
       {tac:'| skip => intro heq; cases heq', h:"<code>intro heq</code> takes the equation, now <code>Cmd.skip = Cmd.loop b₀ c₀</code>. <code>cases heq</code> asks which constructor of <code>Eq</code> could have produced it, finds that the two sides are headed by different constructors of <code>Cmd</code>, and closes the branch with no goals left."},
       {tac:'| assign => intro heq; cases heq', h:"The same line on a much larger goal: <code>Cmd.assign x✝ e✝</code> heads the equation, and below it the final state has been instantiated to the record <code>assign</code> builds, so the goal prints in five lines where <code>skip</code>'s printed in one. None of it is read — the equation at the head is refuted before anything under it matters, which is why all eight of these branches cost the same regardless of what their rule concludes. <code>assign</code> carries no premises and no sub-run, so the branch name stands alone; adding one placeholder reports <code>Too many variable names provided at alternative `assign`: 1 provided, but 0 expected</code>."},
       {tac:'| load _ => intro heq; cases heq', h:"The underscore is the <code>load</code> rule's <code>hl</code> premise. Writing <code>| load =></code> with no placeholder at all also compiles — a short list leaves the remaining premises inaccessible, which costs nothing in a branch that never looks at them. A list that is too <i>long</i> is the error: <code>Too many variable names provided at alternative `load`: 2 provided, but 1 expected</code>."},
       {tac:'| write _ => intro heq; cases heq', h:"Same shape."},
       {tac:'| free _ => intro heq; cases heq', h:"Same shape."},
       {tac:'| seq _ _ _ _ => intro heq; cases heq', h:"Four underscores: two sub-runs and the two induction hypotheses that come with them. Both hypotheses are dead here for the reason the body's is dead in <code>loopTrue</code> — a <code>seq</code> is not a loop, and the equation says so before any of them can be used."},
       {tac:'| iteTrue _ _ _ => intro heq; cases heq', h:"Three: the guard premise, the sub-run, its induction hypothesis."},
       {tac:'| iteFalse _ _ _ => intro heq; cases heq', h:"And the mirror. That is eight branches gone in eight lines."},
       {tac:'| loopFalse hb =>', h:"The rule with no sub-run. <code>hb</code> is its guard premise, <code>BExpr.eval s✝.store b✝ = false</code> — about the derivation's guard, not yet about the theorem's."},
       {tac:'intro heq hI', h:"Both remaining premises, in order: the equation <code>Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀</code> and the invariant at the starting state. The goal is now the bare conjunction."},
       {tac:'cases heq', h:"Both sides are <code>Cmd.loop</code>, so instead of closing the branch this identifies the arguments: <code>b✝</code> becomes <code>b₀</code> and <code>c✝</code> becomes <code>c₀</code> everywhere, and <code>hb</code> is now a statement about the theorem's own guard. No hypothesis is lost, but the surviving two are re-listed in the order <code>cases</code> rebuilt them — <code>hI</code> above <code>hb</code>, the reverse of the order they were introduced in — and the case name gains a <code>.refl</code>."},
       {tac:'exact ⟨hI, hb⟩', h:"The goal is <code>I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false</code> and those are the two hypotheses named on the two lines above, in that order. <code>loopFalse</code>'s final state is its initial state, so no assertion has to be moved anywhere."},
       {tac:'| loopTrue hb hbdy _ _ ihrest =>', h:"Five names, in the order <code>induction</code> supplies them: all three premises first — guard, body run, tail run — then the two induction hypotheses. The third and fourth are underscored: the tail run is only ever reached through its own induction hypothesis, and the body's induction hypothesis cannot be used at all."},
       {tac:'intro heq hI', h:"As before. <code>hI</code> is the invariant at <code>s✝</code>, the state the body starts from; the goal is about <code>s''✝</code>, the state the whole loop ends at."},
       {tac:'cases heq', h:"Identifies the derivation's guard and body with the theorem's, which is what makes <code>hbody</code> applicable to <code>hbdy</code> at all: before this line <code>hbdy</code> is a run of <code>c✝</code> and <code>hbody</code> is about <code>c₀</code>."},
       {tac:'exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)', h:"Read the bracket first. <code>⟨hI, hb⟩</code> is <code>aAnd I (bTrue b₀)</code> at the starting state — the invariant, and the guard that this rule says went true. <code>hbody</code> applied to it and to the body's run gives the invariant at the middle state, which is the second argument <code>ihrest</code> wants; the three underscores before the bracket are the store, the heap and the middle state, all determined by <code>hbdy</code>. <code>rfl</code> is the first argument, because after <code>cases heq</code> the equation <code>ihrest</code> asks for is an identity."},
       {tac:'intro σ h s\' hI hex', h:"<code>partialHoare_while</code> now. The five binders of <code>PartialHoare</code>, exactly as in Unit 35's rules."},
       {tac:'exact loop_invariant hbody hex rfl hI', h:"The helper, at the one instance it was written for. <code>hex</code> supplies the derivation and fixes <code>cmd</code> to <code>.loop b c</code>, so <code>rfl</code> discharges the equation; <code>hI</code> is the invariant at the start. The conclusion is the spelled-out conjunction, and the goal is <code>aAnd I (bFalse b) s'.store s'.heap</code> — the same term, so nothing converts them."}
     ],
     deep:[
       {t:'trace', title:'The two surviving branches, step by step (contexts trimmed to the lines that change)',
        start:"⊢ ∀ {cmd : Cmd} {s s' : State},\n    Exec cmd s s' → cmd = Cmd.loop b₀ c₀ → I s.store s.heap → I s'.store s'.heap ∧ BExpr.eval s'.store b₀ = false",
        steps:[
          {tac:'intro cmd s s\' hex',
           state:"cmd : Cmd\ns s' : State\nhex : Exec cmd s s'\n⊢ cmd = Cmd.loop b₀ c₀ → I s.store s.heap → I s'.store s'.heap ∧ BExpr.eval s'.store b₀ = false",
           h:"Two arrows still in the goal. Everything under them is what the induction gets to generalise."},
          {tac:'| loopFalse hb => intro heq hI',
           state:"case loopFalse\nhb : BExpr.eval s✝.store b✝ = false\nheq : Cmd.loop b✝ c✝ = Cmd.loop b₀ c₀\nhI : I s✝.store s✝.heap\n⊢ I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false",
           h:"Two guards, <code>b✝</code> and <code>b₀</code>, and <code>hb</code> is about the wrong one. Nothing in this branch can close the goal yet."},
          {tac:'cases heq',
           state:"case loopFalse.refl\ns s' s✝ : State\nhI : I s✝.store s✝.heap\nhb : BExpr.eval s✝.store b₀ = false\n⊢ I s✝.store s✝.heap ∧ BExpr.eval s✝.store b₀ = false",
           h:"<code>b✝</code> and <code>c✝</code> are gone from the context and <code>hb</code> now names <code>b₀</code>. The goal is the conjunction of the two hypotheses above it, in order."},
          {tac:'exact ⟨hI, hb⟩',
           h:"The goal above is matched slot for slot and the branch closes. One branch is left."},
          {tac:'| loopTrue hb hbdy _ _ ihrest => intro heq hI; cases heq',
           state:"case loopTrue.refl\nhI : I s✝.store s✝.heap\nhb : BExpr.eval s✝.store b₀ = true\nhbdy : Exec c₀ s✝ s'✝\nihrest :\n  Cmd.loop b₀ c₀ = Cmd.loop b₀ c₀ → I s'✝.store s'✝.heap → I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false\n⊢ I s''✝.store s''✝.heap ∧ BExpr.eval s''✝.store b₀ = false",
           h:"Three states are live: <code>s✝</code> where the invariant is known, <code>s'✝</code> where <code>ihrest</code> wants it, and <code>s''✝</code> where the goal is. <code>hbdy</code> is the run joining the first two, and it is the only thing that can move an assertion across."},
          {tac:'exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)',
           state:"No goals.",
           h:"<code>hbody _ _ _ ⟨hI, hb⟩ hbdy</code> has type <code>I s'✝.store s'✝.heap</code>, and <code>ihrest</code>'s first argument is an identity because <code>cases heq</code> made it one."}
        ],
        done:"No goals."},
       {t:'p', h:"The equation is the only reason eight branches are cheap and two are not, and the direction it is written in is free. State the helper with <code>.loop b₀ c₀ = cmd</code> instead, change nothing else, and both proofs compile as they stand — the eighteen tactic lines of the helper and the two of the rule, whose <code>rfl</code> now proves the equation the other way round: <code>cases</code> on an equation between two constructor applications does the same work whichever way round it is written."},
       {t:'code', tag:'illustration', cap:'The other premise, dropped. Without <code>hbody</code> the statement is refutable at a loop that runs once and stops: the invariant claims variable <code>0</code> holds <code>1</code>, the guard asks whether it is non-zero, and the body sets it to zero. The run is one <code>loopTrue</code> over one <code>loopFalse</code>, both guard premises by <code>rfl</code>; the equation holds and the invariant holds at entry. It fails at the exit, which is the one place <code>hbody</code> would have spoken.',
        src:"example :\n    ¬ (∀ {I : Assertion} {b₀ : BExpr} {c₀ : Cmd} {cmd : Cmd} {s s' : State},\n        Exec cmd s s' → cmd = .loop b₀ c₀ →\n          I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false) := by\n  intro hno\n  have hrun : Exec (.loop (.not (.equals (.var 0) (.const 0))) (.assign 0 (.const 0)))\n      ⟨fun _ => 1, Heap.empty⟩ ⟨Store.set (fun _ => 1) 0 0, Heap.empty⟩ :=\n    Exec.loopTrue rfl Exec.assign (Exec.loopFalse rfl)\n  have h := hno (I := fact (fun σ => σ 0 = 1)) hrun rfl rfl\n  simp [fact, Store.set] at h"},
       {t:'detail', title:'The same proof with nothing left under the arrow', open:false, blocks:[
         {t:'p', h:"Stopping <code>intro</code> after the derivation is a matter of what you can see, not of what compiles. <code>induction</code> reverts any hypothesis mentioning the target's indices before it runs and re-introduces it in every branch, so taking the equation and the invariant up front works too — and the branches then open directly on <code>cases heq</code> with no <code>intro</code> at all."},
         {t:'code', tag:'illustration', cap:'Compiled. Six names on the first line instead of four, eight branches of two words instead of three, and the two survivors lose a tactic each. What it costs is that the goal at the <code>induction</code> line no longer shows what is about to be generalised: the reverting happens, and it happens out of sight.',
          src:"theorem invariantFlat {I : Assertion} {b₀ : BExpr} {c₀ : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b₀)) c₀ I) :\n    ∀ {cmd : Cmd} {s s' : State}, Exec cmd s s' → cmd = .loop b₀ c₀ →\n      I s.store s.heap → I s'.store s'.heap ∧ b₀.eval s'.store = false := by\n  intro cmd s s' hex heq hI\n  induction hex with\n  | skip => cases heq\n  | assign => cases heq\n  | load _ => cases heq\n  | write _ => cases heq\n  | free _ => cases heq\n  | seq _ _ _ _ => cases heq\n  | iteTrue _ _ _ => cases heq\n  | iteFalse _ _ _ => cases heq\n  | loopFalse hb => cases heq; exact ⟨hI, hb⟩\n  | loopTrue hb hbdy _ _ ihrest => cases heq; exact ihrest rfl (hbody _ _ _ ⟨hI, hb⟩ hbdy)"}
       ]}
     ],
     pitfall:"Naming three things in the <code>loopTrue</code> branch instead of five. <code>| loopTrue hb hbdy ihrest =></code> is accepted without complaint, because <code>loopTrue</code> has three premises and your third name lands on the tail run rather than on an induction hypothesis. The two hypotheses then stay inaccessible, and the error surfaces on the last line as <code>Function expected at ihrest but this term has type Exec (Cmd.loop b₀ c₀) s'✝ s''✝</code>. Under <code>induction</code> the order is all premises first, then the induction hypotheses, one for each premise that was itself a derivation — so <code>loopTrue</code> wants five names and <code>seq</code> wants four. · Handing <code>hbody</code> the invariant on its own: <code>exact ihrest rfl (hbody _ _ _ hI hbdy)</code> reports <code>The argument hI has type I s✝.store s✝.heap but is expected to have type aAnd I (bTrue b₀) ?m.303 ?m.304</code>. The body's precondition is the conjunction, not <code>I</code>, and the missing half is <code>hb</code> — the rule's first design decision arriving as a type error. · Dropping the three underscores, <code>hbody ⟨hI, hb⟩ hbdy</code>, reports something stranger: <code>Invalid `⟨...⟩` notation: The expected type `Var → Val` is not an inductive type</code>. <code>PartialHoare</code>'s store, heap and final state are explicit binders, so the first thing you hand it is read as the store. · And <code>cases heq</code> before <code>intro heq</code>, which reports <code>Unknown identifier `heq`</code> followed by <code>Tactic `cases` failed: major premise type is not an inductive type ?m.42</code>; the equation is still under an arrow at the head of every branch.",
     variants:"Delete the equation from the statement and the theorem is false, not unproved — the refutation is compiled above the exercise, at <code>skip</code>, with a satisfiable body premise. · Delete <code>hbody</code> instead and it is false again, at a different kind of command: a loop that terminates after one turn, refuted in the panel above. The two premises fail at different points, and neither can cover for the other — the equation is what excludes commands that are not this loop, <code>hbody</code> is the only thing said about the one that is. · Reverse the equation to <code>.loop b₀ c₀ = cmd</code> and everything compiles unchanged. · Write the conclusion folded, as <code>aAnd I (bFalse b₀) s'.store s'.heap</code>, and the proof still compiles because the two are the same term; what changes is the ten branch displays, which then show <code>aAnd I (bFalse b₀) s✝.store s✝.heap</code> and stop telling you which conjunct each line is producing. · Drop <code>bTrue b₀</code> from the body's premise and the rule stays true and gets harder to use: that is <code>whileStrongBody</code>, derived from this theorem in the section below. · Feed <code>ihrest</code> the invariant you already hold, as <code>exact ihrest rfl hI</code>, and Lean names the exact gap: <code>The argument hI has type I s✝.store s✝.heap but is expected to have type I s'✝.store s'✝.heap</code>. One state apart, and one run of the body between them."
    },

    /* ================================================== reading the rule off ==== */

    {t:'sec', s:'What you know when a loop stops'},

    {t:'p', h:"The rule is the helper applied once, and that application is where the generalisation is paid back. <code>loop_invariant hbody hex rfl hI</code>: <code>hex</code> is the run, and supplying it fixes <code>cmd</code> to <code>.loop b c</code>, which is what makes the equation an identity and <code>rfl</code> a proof of it. The helper was general so that the induction would run; it is used at one command, once, and never again."},

    {t:'p', h:"On exit you hold two facts and the second is the one that makes the rule usable. The invariant alone would tell you nothing you did not know at the start. The guard being false is a fact about the final store that no other rule in the logic produces, and every use of the rule spends it: it is what turns <i>the loop preserved something</i> into <i>the loop finished its job</i>."},

    {t:'code', tag:'illustration', cap:'The two weakenings, now derivable. The first throws the exit fact away by taking the left conjunct; the second accepts the stronger body premise and adapts it to the rule by discarding the guard conjunct with <code>.1</code>. Both are corollaries, and the arrow runs one way only.',
     src:"theorem whileWeakPost {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare (aAnd I (bTrue b)) c I) :\n    PartialHoare I (.loop b c) I :=\n  fun σ h s' hI hex => (partialHoare_while hbody σ h s' hI hex).1\n\ntheorem whileStrongBody {I : Assertion} {b : BExpr} {c : Cmd}\n    (hbody : PartialHoare I c I) :\n    PartialHoare I (.loop b c) (aAnd I (bFalse b)) :=\n  partialHoare_while (fun σ h s' hpre hex => hbody σ h s' hpre.1 hex)"},

    {t:'note', kind:'key', h:"To use the rule you supply one thing: an assertion preserved by the body, given the guard. In exchange the rule hands back the assertion at the exit, together with the negation of the guard. Nothing else about the loop is available and nothing else is needed — the number of iterations never appears in the statement, in the proof, or in what you get out. That is the whole point of an invariant, and it is as much as partial correctness has to say about a loop."},

    {t:'p', h:"One debt falls due here. Unit 35 exhibited a loop whose guard never goes false, asserted that it has no run from any state, and could not prove it: the proof it wanted was an induction over a derivation with a fixed command, and that is what the previous section built."},

    {t:'code', tag:'illustration', cap:'The guard is the one defined above, true at every store, and the body is <code>skip</code> — which is Unit 35\'s <code>spinSkip</code> written out. Take <code>aTrue</code> as the invariant — the body preserves it for nothing — and the rule says the guard is <code>false</code> at the end of any run. It is not, so there is no run. The last line carries that contradiction through the definitions.',
     src:"theorem spinSkip_stuck (s s' : State) :\n    ¬ Exec (.loop guardAlwaysTrue .skip) s s' := by\n  intro hex\n  have hbody : PartialHoare (aAnd aTrue (bTrue guardAlwaysTrue)) .skip aTrue := by\n    intro σ h s'' hp hx\n    cases hx\n    trivial\n  have hpost := loop_invariant hbody hex rfl trivial\n  simp [guardAlwaysTrue, BExpr.eval, Atom.eval] at hpost"},

    {t:'p', h:"So Unit 35's pair of theorems about a command with no run now has its second instance. A command with no run satisfies every partial triple you can write about it and refutes every total one whose precondition is inhabited; the faulting load was the first instance, and a diverging loop is the second. The gap between the two readings is no longer described, it is populated."},

    /* ================================================== a concrete loop ==== */

    {t:'sec', s:'An invariant that owns a cell'},

    {t:'p', h:"Use it on the smallest loop that does anything. One variable, counted down to zero."},

    {t:'code', tag:'verified', cap:'The guard says <i>x is not zero</i>: <code>.equals (.var x) (.const 0)</code> compares the variable with the constant, and <code>.not</code> flips it. The body decrements <code>x</code>, and Unit 18\'s truncated subtraction means it cannot go below zero.',
     src:"def counterGuard (x : Var) : BExpr := .not (.equals (.var x) (.const 0))\n\ndef countdown (x : Var) : Cmd :=\n  .loop (counterGuard x) (.assign x (.minus (.var x) (.const 1)))"},

    {t:'code', tag:'illustration', cap:'The guard at two stores, both by <code>rfl</code>: <code>Atom.eval</code> reads the variable, <code>==</code> compares two naturals, <code>!</code> flips the answer.',
     src:"example : (counterGuard 0).eval (fun _ => 3) = true := rfl\nexample : (counterGuard 0).eval (fun _ => 0) = false := rfl"},

    {t:'p', h:"Now pick an invariant, and pick one the rule can actually be applied with. The obvious candidate — <i>x holds the number of turns remaining</i> — is not available yet, because expressing <i>remaining</i> means naming a quantity that changes, and the rule as stated takes a single assertion. Unit 37 supplies the missing device. What is available now is an assertion the body cannot disturb at all."},

    {t:'p', h:"<code>countdown</code> touches one variable and no memory. So take a heap cell, anywhere, holding anything, and claim that the loop still owns it afterwards. The invariant is <code>l ↦ v</code>: exact ownership of one cell, which is the assertion Unit 13 built. The body is an assignment, and an assignment writes to the store and never to the heap."},

    {t:'p', h:"That fixes everything the rule needs except its premise, which here is a triple about a single assignment: assuming <code>l ↦ v</code> and the guard, one run of the body leaves <code>l ↦ v</code>. Proving it is the exercise."},

    {t:'ex',
     id:'x72',
     name:'countdown_keeps_cell',
     why:"The rule from the previous exercise, applied. It also isolates the two halves of verifying a loop: this exercise is <i>find the invariant and prove the step</i>, with termination deliberately off the table, and Unit 37's <code>countdown_spec</code> is the same loop with the other half supplied. The invariant here is an ownership claim rather than a fact about the store, which is the smaller half of the shape Unit 37's capstone needs — there the invariant is a store fact and a <code>↦</code> conjoined, and the step obligation has to rewrite the heap. Here nothing touches the heap, so the ownership half can be met on its own first.",
     setup:"<code>counterGuard</code> and <code>countdown</code> are given above. <code>partialHoare_while</code> is the theorem from the previous exercise; <code>(I := …)</code> supplies its invariant by name, as Unit 22 supplied <code>hoare_seq</code>'s middle assertion.",
     goal:"theorem countdown_keeps_cell (x : Var) (l : Loc) (v : Val) :\n    PartialHoare (l ↦ v) (countdown x) (aAnd (l ↦ v) (bFalse (counterGuard x))) := by",
     hints:[
       "Unfolded, the goal says: for every store, every heap and every final state, if the heap is exactly the cell <code>l</code> holding <code>v</code>, and <code>countdown x</code> runs from there to that final state, then the final heap is exactly that same cell and <code>counterGuard x</code> evaluates to <code>false</code> at the final store. Nothing is claimed about how many turns the loop took, and nothing is claimed about <code>x</code> — only about the guard.",
       "<code>countdown x</code> is a loop, and the postcondition is already an <code>aAnd</code> of the precondition with a <code>bFalse</code> of the guard, which is the shape the loop rule concludes with. So the statement is an instance of the rule and all that is left is its premise: a triple about the body — one assignment — with <code>l ↦ v</code> and the guard as its precondition and <code>l ↦ v</code> as its postcondition. An assignment changes the store and nothing else, and <code>l ↦ v</code> is a claim about the heap alone.",
       "The lemma is <code>partialHoare_while</code>, and the tactic that applies it while leaving its premise open as a goal is <code>refine</code>. After that: the usual five <code>intro</code>s, inversion on the run of the assignment, and one component of the precondition pair.",
       "<code>refine partialHoare_while (I := (l ↦ v)) ?_</code>, then <code>intro σ h s' hpre hex</code>, then <code>cases hex</code>. What is left is <code>l ↦ v</code> at the state the assignment produced, and <code>hpre.1</code> is <code>l ↦ v</code> at the state it started from — the same claim, because <code>↦</code> ignores the store."
     ],
     sol:"theorem countdown_keeps_cell (x : Var) (l : Loc) (v : Val) :\n    PartialHoare (l ↦ v) (countdown x) (aAnd (l ↦ v) (bFalse (counterGuard x))) := by\n  refine partialHoare_while (I := (l ↦ v)) ?_\n  intro σ h s' hpre hex\n  cases hex\n  exact hpre.1",
     solNote:"<code>(I := (l ↦ v))</code> can be dropped: the postcondition <code>aAnd (l ↦ v) (bFalse (counterGuard x))</code> determines the invariant by matching, and the proof compiles without it. It is written because the invariant is the entire content of the verification, and a proof of a loop that does not say what its invariant is has hidden its own idea.",
     expl:"One application and a three-line premise. <code>refine</code> matches the goal against the rule's conclusion, which fixes the invariant, the guard and the body all at once, and leaves the body obligation as a hole. That obligation is discharged by inverting the assignment: the resulting state has the same heap, <code>l ↦ v</code> is a claim about the heap, and the guard conjunct of the precondition is never consulted.",
     walk:[
       {tac:'refine partialHoare_while (I := (l ↦ v)) ?_', h:"Matching the goal against <code>PartialHoare I (.loop b c) (aAnd I (bFalse b))</code> unfolds <code>countdown x</code> to its <code>.loop</code>, which fixes <code>b</code> to <code>counterGuard x</code> and <code>c</code> to the assignment. The hole left is the rule's premise: <code>PartialHoare (aAnd (l ↦ v) (bTrue (counterGuard x))) (Cmd.assign x ((Atom.var x).minus (Atom.const 1))) (l ↦ v)</code>."},
       {tac:'intro σ h s\' hpre hex', h:"The five binders of a partial triple. <code>hpre</code> is the pair — the cell, and the guard — and <code>hex</code> is a run of the assignment. The goal is <code>(l ↦ v) s'.store s'.heap</code>, and nothing yet says what <code>s'</code> is."},
       {tac:'cases hex', h:"One rule concludes a run of an assignment, so inversion has one branch and it removes <code>s'</code> from the context, replacing it in the goal by the state the rule builds: the store updated at <code>x</code>, the heap untouched. That goal prints in eleven lines of nested records; what matters in it is that the heap slot is the <code>h</code> the triple started with."},
       {tac:'exact hpre.1', h:"<code>hpre.1</code> is <code>(l ↦ v) σ h</code>, which unfolds to <code>h = Heap.singleton l v</code>. The goal unfolds to the same equation, because <code>pointsTo</code> discards its store argument. The second component of <code>hpre</code> — the guard — is never used, and dropping <code>bTrue</code> from the rule's premise would not have been noticed here."}
     ],
     deep:[
       {t:'trace', title:'countdown_keeps_cell, four steps (contexts trimmed to what changed)',
        start:"x : Var\nl : Loc\nv : Val\n⊢ PartialHoare (l ↦ v) (countdown x) (aAnd (l ↦ v) (bFalse (counterGuard x)))",
        steps:[
          {tac:'refine partialHoare_while (I := (l ↦ v)) ?_',
           state:"x : Var\nl : Loc\nv : Val\n⊢ PartialHoare (aAnd (l ↦ v) (bTrue (counterGuard x))) (Cmd.assign x ((Atom.var x).minus (Atom.const 1))) (l ↦ v)",
           h:"The loop is gone. What is left mentions the body only, which is the whole economy of the rule: one obligation about one command, in exchange for a statement about an unbounded run."},
          {tac:'intro σ h s\' hpre hex',
           state:"σ : Store\nh : Heap\ns' : State\nhpre : aAnd (l ↦ v) (bTrue (counterGuard x)) σ h\nhex : Exec (Cmd.assign x ((Atom.var x).minus (Atom.const 1))) { store := σ, heap := h } s'\n⊢ (l ↦ v) s'.store s'.heap",
           h:"<code>hpre</code> is about <code>σ</code> and <code>h</code>; the goal is about <code>s'</code>. Offering <code>hpre.1</code> here is refused with <code>hpre.left has type (l ↦ v) σ h but is expected to have type (l ↦ v) s'.store s'.heap</code>."},
          {tac:'cases hex',
           state:"case assign\n⊢ (l ↦ v)\n    {\n        store :=\n          { store := σ, heap := h }.store.set x\n            (Atom.eval { store := σ, heap := h }.store ((Atom.var x).minus (Atom.const 1))),\n        heap := { store := σ, heap := h }.heap }.store\n    {\n        store :=\n          { store := σ, heap := h }.store.set x\n            (Atom.eval { store := σ, heap := h }.store ((Atom.var x).minus (Atom.const 1))),\n        heap := { store := σ, heap := h }.heap }.heap",
           h:"Shown without its six context lines, which are unchanged. The same five-line record appears twice, once as the store argument and once as the heap argument, and only the second is read: <code>pointsTo</code> discards the first, and the second reduces to <code>h</code>."},
          {tac:'exact hpre.1',
           state:"No goals.",
           h:"Accepted without any rewriting. The two terms are definitionally equal once the projections reduce, which is why a goal that prints in eleven lines closes on a hypothesis that prints in one."}
        ],
        done:"No goals."},
       {t:'code', tag:'illustration', cap:'Why the invariant has to be one the body cannot move. Put a store fact where the ownership claim was and the step obligation is refutable: at the store where every variable holds 3 both halves of the precondition are <code>rfl</code>, the run of the body is <code>Exec.assign</code>, and one decrement later <code>x</code> holds 2. The four lines of the exercise work because <code>↦</code> never looks at the store, not because the loop is gentle.',
        src:"example (x : Var) :\n    ¬ PartialHoare (aAnd (fact (fun σ => σ x = 3)) (bTrue (counterGuard x)))\n        (.assign x (.minus (.var x) (.const 1))) (fact (fun σ => σ x = 3)) := by\n  intro hstep\n  have h := hstep (fun _ => 3) Heap.empty _ ⟨rfl, rfl⟩ Exec.assign\n  simp [fact, Store.set, Atom.eval] at h"},
       {t:'p', h:"The second conjunct of the postcondition looks like syntax and is not. <code>bFalse (counterGuard x)</code> says <code>(counterGuard x).eval σ = false</code>, and <code>counterGuard x</code> is <code>.not (.equals (.var x) (.const 0))</code>, so the assertion says that the negation of <i>x equals zero</i> is false — which is to say that <code>x</code> is zero."},
       {t:'code', tag:'illustration', cap:'The postcondition, taken apart. One <code>simp</code> through the definitions turns the guard conjunct into an equation about the store. Both facts come out of the same theorem: you still own the cell, and the counter reached zero.',
        src:"example (x : Var) (l : Loc) (v : Val) (σ : Store) (h : Heap)\n    (hpost : aAnd (l ↦ v) (bFalse (counterGuard x)) σ h) :\n    h = Heap.singleton l v ∧ σ x = 0 := by\n  refine ⟨hpost.1, ?_⟩\n  have hb := hpost.2\n  simp [bFalse, counterGuard, BExpr.eval, Atom.eval] at hb\n  exact hb"}
     ],
     pitfall:"Writing <code>exact hpre</code> in place of <code>exact hpre.1</code> after the inversion. The report is a type mismatch whose expected side runs to eleven lines of nested records, and the temptation is to read those eleven lines as the problem and start unfolding. They are not: the mismatch is that <code>hpre</code> is a conjunction and the goal is one of its conjuncts. When a goal display is mostly projections, check the shape of what you are offering before you attack the display. · Skipping <code>cases hex</code> and going straight to <code>exact hpre.1</code> is the other one, and it reports the honest version of the same gap: <code>hpre.left has type (l ↦ v) σ h but is expected to have type (l ↦ v) s'.store s'.heap</code>. Nothing has told Lean where the run ended.",
     variants:"Change the invariant to <code>emp</code> and the same four lines compile, because <code>emp</code> also reads only the heap. Change it to <code>fact (fun σ => σ x = 3)</code> and the step obligation is refutable, as the panel above compiles it — so the invariant has to be one the body cannot move, or else indexed, which is Unit 37. · Replace the body by <code>.write l (.const 0)</code> and the step obligation fails at the heap, at every value but one: the run's final heap is <code>Heap.write h l 0</code> and the invariant asks for <code>h</code> itself, so at <code>v = 1</code> the two heaps disagree at <code>l</code> — <code>some 0</code> against <code>some 1</code>, which <code>congrFun</code> at <code>l</code> exposes in one line. At <code>v = 0</code> the obligation is true and stops being provable by <code>exact hpre.1</code>: <code>Heap.write (Heap.singleton l 0) l 0</code> and <code>Heap.singleton l 0</code> are the same function written two ways, so the proof needs <code>funext</code> and a <code>simp</code>. Repairing the general case is what Unit 37's capstone does, by indexing the invariant so that the cell is allowed to change in a controlled way. · Drop the <code>bFalse</code> conjunct from the postcondition and the statement is still provable — by <code>whileWeakPost</code> above — and says only that a heap cell survived a loop, with no way to tell that the loop finished."
    },

    {t:'p', h:"The theorem does not say <code>countdown</code> stops. Replace the decrement by <code>.plus (.var x) (.const 1)</code> and the same four lines prove the same triple of the loop you get — a loop that, from any store where <code>x</code> is not zero, never stops at all. Nothing in the proof looked at the body's arithmetic: it spent one fact about the body and the shape of the two rules that conclude a loop run, and neither of those mentions how many turns there are."},

    {t:'dod', h:"You can state the invariant rule, say what each of its two guard conjuncts is for, and derive the two weaker rules that drop them. You can start the proof with <code>cases</code>, close the <code>loopFalse</code> branch, and say precisely what the <code>loopTrue</code> branch is short of. You can read <code>Invalid target</code> off the direct induction, name the offending index, and name the second one that only appears after <code>intro σ h</code>. You can strengthen a statement by quantifying its indices and adding an equation, and refute the version that skips the equation. You can kill eight branches with one line each and say why the line works, read both induction hypotheses in the tenth, say which is dead and why the rule's premise is its replacement. And you can apply the rule to a loop, choose an invariant the body cannot touch, and unpack what the postcondition tells you when the loop stops."},

    {t:'p', h:"Partial correctness is silent about termination — and a loop that never runs satisfies every partial specification you can write. Buying termination back costs one natural number."}

  ]
});
