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

We will clarify that the constants 2 and 3, which are omitted from the differential slice, are included by our backward analysis. We will also improve the colour choices so that they render better in black-and-white.

