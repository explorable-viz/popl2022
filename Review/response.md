We thank our three reviewers for their valuable input. We accept all the notational suggestions and minor corrections; the discussion below covers the remaining issues of clarity and presentation.

### Reviewer A

Your understanding of the figure is correct (assuming you mean Fig 2). We will clarify that the initial visual selection is the value of y in the record {x: "USA", y: 196.7 } passed to BarChart, and will also give the visual selection induced in the LineChart. Fig 1 does not involve the De Morgan dual, but shows how different visual selections induce different data selections; we will make sure this is clear.

In the differential slicing example, we will clarify that our backwards analysis selects the constants 2 and 3 which are omitted from the differential slice.

### Reviewer B

"Prefix" here means partial tree, i.e. a tree from which some subtrees have been deleted. The meaning of "partial value" (L222) is similar: we mean that some initial portion (prefix) of a value is matched by an eliminator, with variables bound to the unmatched parts. We will make sure that this is clear.

There should technically be a typing rule for κ which delegates to the judgement for e or σ as appropriate. Our overloaded \vdash makes this hard to formulate, so we will either add some clarifying text or remove the overloading and add the rule. We will also pick a different arrow symbol for eliminator typing.

Higher-order data presents no complications, but for our current application we only need to track how data flows "through" operations. We expect higher-order data to be important for other applications, such as extracting expression provenance; we will mention this in section 6.1.

Thank you for spotting that (as suggested by Def. 3.2) Fig 8 is a preorder, not a partial order. As it happens, we feel that the presentation would be improved if we dropped □ (and the associated preorder). These were motivated purely by performance, but it seems clear now that other techniques, such as memoisation, may address this without the complexity of holes. It therefore seems premature to presuppose a hole-based approach in the paper. If our reviewers are amenable, we will drop Fig. 8 and the various □ rules and related exposition, and use the space gained to do a better job of explaining the core analysis. As Reviewer C notes, this could be clearer and would benefit from some examples. (We will include a note explaining how our implementation currently works, but make it clear that other choices are possible.)

Thank you for the Pombrio et al. reference; this looks like exactly what we would like to do.

### Reviewer C

The presentational simplification we propose above (relating to □) will provide some space for examples in sections 2 and 3 and some opportunities to simplify the exposition.

Lenses do seem intuitively related, in that the round-tripping properties of Galois connections resemble some of the get/put laws of lenses. We are not aware of any work that establishes a formal relationship.

In "e : e'", the colon indicates cons, whereas in "x: e" the colon associates a field name with a value in a record, so the different spacing is arguably justified; we will try to reduce the risk of confusion.

"x * 0" also does not depend on x. Primitive operations must provide a Galois connection for every application to specific arguments, and if one of them is the annihilator (for operations which have one), our implementation will establish a dependency only on the other argument. A potentially unintuitive case is that 0 * 0 must fix either one or both of the zeroes to depend on; depending on both seems inconsistent with the x * 0 and 0 * x cases (for non-zero x), and depending on just one requires making a choice which might seem arbitrary.
