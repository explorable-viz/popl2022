We thank our three reviewers for their valuable input. We accept all their notational suggestions and do not discuss them below.

### Reviewer A

Your understanding of the figure is exactly right, assuming you mean Fig 2, not Fig 1. We will clarify that the initial visual selection is the value of y in the record {x: "USA", y: 196.7 } passed to BarChart, and will also be specific about the visual selection induced in the LineChart. The mediating data selection consists of the orange fields highlighted in the middle of Fig 2. (Fig 1 does not involve the De Morgan dual, but shows how different visual selections induce different data selections; we will make sure this is clear.)

The type signatures in the Galois connection for Theorem 3.8 are indeed missing "\times \mathcal{A}" on the output (for the upper adjoint) and the input (for the lower adjoint). Theorem 3.11 (line 820) needs a similar fix.

We will clarify that in the differential slicing example that the constants 2 and 3, which are omitted from the differential slice, are included by our backward analysis (because they are "needed").

### Reviewer B

"Prefix" here means a partial tree, i.e. a tree from which some subtrees have been deleted. The meaning of "partial value" (L222) is actually very similar: we mean that only some initial portion (prefix) of a value is matched by an eliminator, with variables bound to the unmatched parts. We will make sure that this is as clear as possible, and avoid redundant terminology.

Indeed there should technically be a typing rule for κ which delegates to the judgement for e or σ as appropriate. Our overloaded typing judgement makes this hard to formulate in a non-confusing way; we will either add some clarifying text or remove the overloading so that we can add the judgement.

We will pick a different arrow symbol for eliminator types to avoid confusion in the typing judgement.

There are no complications with supporting higher-order data, but to support our current application we do not need to track dependencies on operations, but only "through" operations. We do expect tracking higher-order data to be important for other applications, such as extracting expression provenance; we will mention this in section 6.1.

Figure 8 is a preorder, not a partial order: good point! This should have been obvious from Def. 3.2. Thank you for spotting this.

In fact, we feel that the presentation would actually be improved if we dropped □ (and the associated preorder). These were motivated purely by performance, but we now have good reason for thinking that other techniques, such as memoisation, might address this without the complexity of holes. It seems premature therefore to presuppose a hole-based approach in the paper. If our reviewers are amenable, we will drop Fig. 8 and the various □ rules and related exposition, and use ~3/4 page gained to do a better job of explaining the core analysis, which as Reviewer C notes, would benefit from more clarity and some examples. (We will also include a note explaining how our implementation currently works, but make it clear that other choices are possible.)

Use of \tt instead of \top in L544: in fact this can only be \top, since the definition is polymorphic in A. This is a hangover from an earlier less generic formulation.

Thank you for the Pombrio et al. reference; this looks like exactly what we would like to do.

### Reviewer C

We agree with the general point about examples and clarity of the technical sections. The presentational simplification we propose above (relating to □) would provide some space for examples and we will strive to make the text easier to understand.

Lenses do seem intuitively related, in that the round-tripping properties of Galois connections resemble some of the get/put laws of lenses. We are not aware of any work that establishes a formal relationship.

Spacing in "e : e'" vs. "x: e": the first operator is a cons, and the second associates a field name with a value in a record, so the different spacing is arguably justified here. However, it would be more consistent to write the ":" in record notation using code font, as per the cons.

"x * 0" also does not depend on x. A primitive operation such as * must provide a Galois connection for every application of * to specific arguments, and if one of the arguments is the annihilator (for operations which have one), our implementation will establish a dependency only on the other argument. A potentially unintuitive case is that 0 * 0 must fix either one or both of the zeroes to depend on; depending on both seems inconsistent with the x * 0 and 0 * x cases (for non-zero x), and depending on just one requires making a choice which might seem arbitrary.
