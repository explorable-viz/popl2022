We thank our three reviewers for their valuable input.

### Reviewer A

> I could use more details on how Figure 1 is generated: I understand that a
> certain visualization set was fed to the backward analysis, yielding a source
> set (spanning both the program and the table in Figure 1), which was fed in
> turn to the De Morgan dual of the forward analysis. If that's correct, I just
> want a more concrete description of what visualization set and what source set.

Your understanding is exactly right. We will clarify that [...]

> I was confused by [Sel notation] for several minutes. Please parenthesize

> It's confusing to use the letters $f$ and $g$ both for the halves of a Galois connection and for a Galois connection.

Agreed; we will fix this.

> L806: What about the ambient availability?

Well spotted: the type signatures of the Galois connections here are missing "\times \mathcal{A}" on the output (for the upper adjoint) and the input (for the lower adjoint). Theorem 3.11 (line 820) needs a similar fix.

> Figure 13,14: Yellow is hard to see in black-and-white; please choose a darker color.
> L1028: Say more explicitly how your analysis computes better dependency information.

We will clarify that in this example the constants 2 and 3, which are omitted from the differential slice, are included by our backward analysis. We will also improve the colour choices so that they render better in black-and-white.

### Reviewer B

> line 151: what is meant by "prefixes"?

"Prefix" here means a partial tree, i.e. a tree from which some subtrees have been deleted. We will clarify this.

> line 222:  what is a "partial" value?

The meaning here is similar to "prefix": we mean that only some initial portion (prefix) of a value is matched by an eliminator. We will make sure that this is as clear as possible, and will avoid redundant terminology.

> line 246: no typing rule for k?

[Assuming you mean κ here.] Indeed there should technically be a typing rule for κ which delegates to the judgement for e or σ as appropriate. Our overloaded typing judgement makes this hard to formulate; we will either add some clarifying text or remove the overloading and add the judgement.

> line 259: I found the overloading of --> in this judgment confusing in parts of the exposition.

We will pick a different arrow symbol for eliminator types to avoid this problem.

> line 355: please distinguish the metalanguage and object language phi.

Agreed, it is not clear here whether 𝜙(n) is intended to denote a piece of syntax or a mathematical value. A convention such as \hat{\phi} should help here.

> line 422: are there any complications to supporting higher-order data?

There are no complications, but to support our current application we do not need to track dependencies on operations (but only "through" operations). We do expect tracking higher-order data to be important for other applications, such as extracting expression provenance; we will mention this in section 6.1.

> line 453:  The figure is a preorder on values, not a partial order.
> line 494: Figure 8 is a preorder

Good point! This should have been obvious from Def. 3.2. Thank you for spotting this.

In hindsight, we feel that the presentation would be improved if we in fact dropped □ (and the associated preorder), which were motivated purely by performance. Experience with our implementation has made it clear that other techniques, such as memoisation, might address this while avoiding the complexity of holes, so it seems premature to presuppose a hole-based approach in the paper. If our reviewers are amenable, we will simplify the presentation by dropping Fig. 8 and the various □ rules and related exposition, and use the space gained (about 3/4 of a page) to do a better job of explaining the core analysis. As Reviewer C notes, this section would benefit from some examples. (We will certainly include a note explaining how our implementation currently works, but make it clear that other choices are possible.)

> line 457:  please clarify the presentation of the two-point lattice,
> including which elements are in the set (rather than reusing "2"), and
> what the elements in the tuple represent (which was not explained
> earlier).
> line 903:  again the name "2" is used for both the algebra and the
> carrier set.  Just enumerate the elements of the carrier.

We will write the carrier as {tt, ff} and clarify the role of each.

> line 473: I did not find the reference to representable functors
> helpful.  Just say that comparison is defined pointwise and give an
> example.

Agreed, the reference could be elided with no loss of clarity.

> line 544: for the var case, perhaps use \top instead of tt, to be more generic

In fact this can only be \top, since the definition is polymorphic in A. This is a hangover from an earlier less generic formulation.

> line 1174: Related to this is work on Resugaring by Pombrio et al.

Thank you for this reference; this looks like exactly what we would like to do.

### Reviewer C

> The paper could do with more giving examples of concepts before diving into the
> theory of the concepts.
> At about section 2.2.4, I started getting lost and would have found it useful
> to have some examples.
> At about section 3.1, I have another note that I was starting to get lost

These sections are dense and would benefit from some examples. The presentational simplification we propose above (relating to □) would provide some space to do that.

> How does this work relate to lenses?

Lenses do seem intuitively related, in that the round-tripping properties of Galois connections resemble some of the get/put laws of lenses. We are not aware of any work that establishes a formal relationship.

> L177: It would be useful to call out why eliminators are used by this language

We will make this clearer.

> L179: "e : e'" has space before ":" but "x: e" does not.  This seems inconsistent.

[Assuming you mean L189 here.] The first operator is a list cons, and the second is syntax that associates a field name with a value in a record, so the missing space is (arguably) justified here, although some prefer to write cons with no space on either side. However, it would be more consistent to write the ":" in record notation using code font, as we do with the cons.

> The paper notes that "0 * x" does not depend on "x".  Does "x * 0" depend on "x"
> or is there a way you can get the best of both cases?

"x * 0" does not depend on x either. A primitive operation such as * must provide a Galois connection for every application of * to specific arguments (section 3.2.2), and if one of the arguments is the annihilator (for operations which have one), our implementation will in that case establish a dependency only on the other argument. An (arguably) unintuitive case is that 0 * 0 must fix either one or both of the zeroes to depend on; depending on both seems inconsistent with the x * 0 case (for non-zero x), and depending on just one requires making a choice which might seem arbitrary.
