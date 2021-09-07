# Reviewer response

## Instructions

> The rebuttal period have just started. It goes from the beginning of 4
> Aug (Sat, AOE), until the end of 8 Aug (Wed, AOE).

> Your response is optional. A response must be concise, addressing
> specific points raised in review; in particular, it must not introduce
> new technical results. The soft limit of a response is 500 words. This
> means that reviewers will not be expected to read texts beyond this
> 500-word limit.

## Response to reviewers

We thank our three reviewers for their valuable input.

### Reviewer: A

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

### Reviewer: B

> line 151: what is meant by "prefixes"?

"Prefix" here means a partial tree, i.e. a tree from which some subtrees have been deleted. We will clarify this.

> line 222:  what is a "partial" value?

The meaning here is similar to "prefix": we mean that only some initial portion (prefix) of a value is matched by an eliminator. We will make sure that this is as clear as possible, and will avoid redundant terminology.

> line 246: no typing rule for k?

[Assuming you mean κ here.] Indeed there should technically be a typing rule for κ which delegates to the judgement for e or σ as appropriate. Our overloaded typing judgement makes this hard to formulate; we will either add some clarifying text or remove the overloading and add the judgement.

> line 259: I found the overloading of --> in this judgment confusing in parts of the exposition.

We will pick a different arrow symbol for eliminator types to avoid this problem.

> line 355: please distinguish the metalanguage and object language phi.

Agreed, it is not clear here whether 𝜙(n) is a piece of syntax or a mathematical value (interpreted as a piece of syntax). A convention such as \hat{\phi} should help here.

> line 422: are there any complications to supporting higher-order data?

There are no complications, but to support our current application we do not need to track dependencies on operations (but only "through" operations). We do expect tracking higher-order data to be important for other applications, such as extracting expression provenance; we will mention this in section 6.1.

> line 453:  The figure is a preorder on values, not a partial order.
> line 494: Figure 8 is a preorder

Good point! This should have been obvious from Def. 3.2. Thank you for spotting this.

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

Thank you for this reference; this indeed exactly what we would like to do.
