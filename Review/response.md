We thank our three reviewers and accept all their notational suggestions and minor corrections.

As a general comment, we feel the presentation would be improved if we dropped □ and the associated ordering (which as Reviewer B notes is actually a preorder, not a partial order). These details were motivated by performance, but it now seems clear that other implementation techniques (e.g. memoisation) may address this while avoiding the complexity of holes. It therefore seems premature to presuppose a hole-based implementation for the paper. If reviewers are amenable, we will drop Fig. 8 and the various □ rules and related exposition, and use the space to do a better job of explaining the core analysis. As Reviewer C notes, these sections could be clearer and would benefit from some examples.

### Reviewer A

Your understanding of the figure is correct, if you mean Fig 2. The initial visual selection is the value of y in the record {x: "USA", y: 196.7} passed to BarChart; we will clarify this and do the same for the LineChart. Fig 1 does not involve the De Morgan dual, but shows how different visual selections induce different data selections; we will make sure this is clear.

### Reviewer B

"Prefix" here means a term tree from which some subtrees have been deleted. "Partial value" (L222) is similar, referring to the initial portion (prefix) of a value matched by an eliminator, with variables bound to the unmatched parts. We will make sure these are clear.

There should technically be a typing rule for κ which delegates to the judgement for e or σ as appropriate, but overloading \vdash makes this hard to formulate. We will add some clarifying text, or avoid overloading and add the rule. We will also pick a different arrow symbol for eliminator typing.

Higher-order data presents no complications, but for our current application we only need to track how data flows "through" operations. We expect higher-order data to be important for applications such as expression provenance; we will mention this in section 6.1.

### Reviewer C

Lenses do seem intuitively related, in that the round-tripping properties of Galois connections resemble the get/put laws of lenses. We are not aware of any work that establishes a formal relationship.

In _e : e'_, the colon indicates cons, whereas in _x: e_ the colon associates a field name with a value in a record, so the different spacing is arguably justified. We will try to reduce the risk of confusion here.

x * 0 also does not depend on x. Binary primitives must provide a Galois connection for every pair of arguments; if one is the annihilator (for operations which have one), our implementation will establish a dependency only on the other argument. A potentially unintuitive case is that 0 * 0 must fix either one or both of the zeroes to depend on; depending on both seems inconsistent with x * 0 and 0 * x (for non-zero x), but depending on just one requires making a choice which might seem arbitrary.
