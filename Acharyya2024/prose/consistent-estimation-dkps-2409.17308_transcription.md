# Consistent estimation of generative model representations in the data kernel perspective space

**Authors:** Aranyak Acharyya, Michael W. Trosset, Carey E. Priebe, Hayden S. Helm
**arXiv:** 2409.17308v2
**Date:** last revised 2025-01-17
**Source:** https://arxiv.org/abs/2409.17308

**Transcription note:** Foundational DKPS consistency paper. This transcription is intended for Lean formalization scaffolding and statement/proof alignment review.

This file is an automatically generated Markdown transcription from the arXiv PDF using `pdftotext -layout`. It preserves page breaks and much of the equation/table layout as plaintext. For formal proof work, verify theorem statements and proof-critical equations against the PDF or TeX source.

## Page 1

```text
                                                  Consistent estimation of generative model
                                             representations in the data kernel perspective space


                                                 Aranyak Acharyya                  Michael W. Trosset                  Carey E. Priebe
                                              Johns Hopkins University              Indiana University             Johns Hopkins University
                                                aachary6@jhu.edu                 mtrosset@indiana.edu                   cep@jhu.edu
arXiv:2409.17308v2 [cs.LG] 17 Jan 2025




                                                                                      Hayden S. Helm
                                                                                      Helivan Research
                                                                                    hayden@helivan.io



                                                                                         Abstract

                                                     Generative models, such as large language models and text-to-image diffusion
                                                     models, produce relevant information when presented a query. Different mod-
                                                     els may produce different information when presented the same query. As the
                                                     landscape of generative models evolves, it is important to develop techniques to
                                                     study and analyze differences in model behaviour. In this paper we present novel
                                                     theoretical results for embedding-based representations of generative models in the
                                                     context of a set of queries. In particular, we establish sufficient conditions for the
                                                     consistent estimation of the model embeddings in situations where the query set
                                                     and the number of models grow.


                                         1    Introduction
                                         Generative models have gained popularity in natural language processing [4, 21], text-to-image
                                         generation [7], and code generation [25], as well as in other domains [1, 22]. The key feature
                                         of these models is their ability to generate relevant responses to wide-ranging queries. Based on
                                         differences such as pre-training data mixture, architecture, size, etc., the responses of different models
                                         (or of different generation configurations of the same model) may vary widely. Recently, empirical
                                         investigations have demonstrated the potential of embedding-based vector representations of models
                                         for capturing meaningful differences in model behavior in the context of a set of queries [11, 9, 13].
                                         Following [13], the resulting representations are referred to as perspectives of the models and the
                                         space in which the representations reside is referred to as the perspective space of the models.
                                         In this paper we provide theoretical justification for these successful empirical investigations by
                                         arguing that the estimated perspective space is consistent for a population-level perspective space.
                                         In particular, we analyze three different – progressively more complicated – settings in which the
                                         perspective space can be used: i) fixed collection of models and fixed set of queries; ii) fixed collection
                                         of models and growing set of queries; and iii) growing collection of models and growing set of
                                         queries. For each setting we show that the multi-dimensional scaling with the raw stress criterion of a
                                         collection of matrix representations yields vectors that are consistent for an appropriately defined
                                         limiting configuration. Importantly, we provide sufficient conditions for consistency as a function of
                                         the generative properties of each model.
                                         Our work is a part of two major bodies of literature: embeddings of inputs and outputs of generative
                                         models [16, 20, 17, 19] and embedding complex objects in suitable Euclidean spaces via multi-
                                         dimensional scaling [3, 24, 14, 5]. In particular, the perspective space is a minimizer of the raw stress
                                         criterion [15] for a dissimilarity matrix or function [23] defined on a set of matrix representations of
                                         generative models whose rows correspond to the average embedded response for a particular query.
                                         Preprint.
```

## Page 2

```text
The rest of the paper is organized as follows. In Section 2 we introduce notation and review multi-
dimensional scaling by the raw stress embedding criterion. We describe our setting in Section 3 and
then establish our main theoretical results in Section 4. We provide numerical evidence to support
the theoretical results in Section 5 and discuss our results, potential applications, and extensions in
Section 6.
Contribution. We build upon recent theoretical results related to multi-dimensional scaling via the
raw stress criterion. In particular, we provide sufficient conditions for the consistency of sampling-
based vector representations of black-box generative models. Our results are general to collections of
generative models whose outputs can be mapped to a shared embedding space.

2     Preliminaries
2.1   Notations
Bold letters (such as B or µ) are used to represent vectors and matrices. Any vector by default is a
column vector. For a matrix B, the j-th row is denoted by (B)j· , and the (i, i′ )-th entry is denoted by
Bii′ . Moreover, ∥B∥F denotes the Frobenius norm of the matrix B. For any two vectors x and y,
∥x − y∥ denotes the Euclidean distance between x and y. The set of d × d orthogonal matrices is
denoted by O(d).

2.2   Multidimensional scaling by raw stress embedding
Multidimensional scaling [3] refers to the family of methods that produce vector representations of a
set of objects from their pairwise dissimilarities. Raw stress embedding [15, 23] is a popular method
for multidimensional scaling. For our purposes, we discuss raw stress embedding in the context of
two scenarios: finite sample size and infinite sample size. The following is adapted from [23] for our
specific setting of collections of generative models.
Finite sample size: Let us assume there are n objects and that the matrix ∆(∞) ∈ Rn×n is
           (∞)
such that ∆ij is the dissimilarity between the i-th object and the j-th object for i, j ∈ [n]. For
a given embedding dimension d ∈ N, our goal is to find vectors ψ 1 , . . . ψ n ∈ Rd such that
                (∞)
 ψ i − ψ j ≈ ∆ij . We define solutions to this problem as:
                                         n                             2
                                                                  (∞)
                                         X
         (ψ 1 , . . . ψ n ) = arg min             ∥zi − zi′ ∥ − ∆ii′         .                       (1)
                               zi ∈Rd
                                        i,i′ =1

We let ψ ∈ Rn×d denote the matrix whose i-th row is ψ i and write ψ = mds(∆(∞) ).
Remark 1. Given dissimilarity matrix ∆(∞) , ψ = mds(∆(∞) ) is not unique – an affine transfor-
mation upon a minimizer gives another minimizer. We denote the set of all solutions mds(∆(∞) ) by
MDS(∆(∞) ). Apart from affine transformations of a solution, there may be two different minimizers
that are not affine transformation of each other.
Remark 2. Note that
              n                       2               2
                                   (∞)
            X
       min          ∥zi − zi′ ∥ − ∆ii′          ˜ − ∆(∞) ,
                                          = min ∆
         zi ∈Rd                                         ˜
                                                        ∆                        F
                  i,i′ =1

where ∆˜ is varied over the set of all n × n Euclidean distance matrices. From the proof of Theorem
2 in [23], it can be argued that it is enough to vary ∆ ˜ over Yn , the set of all n × n Euclidean
distance matrices with Frobenius norm less than or equal to ∆(∞) , which is closed, bounded,
                                                                       F
and complete. This guarantees the existence of a solution to Eq. (1).

Infinite sample size: In this case, the goal is to find Euclidean representations of all objects from
a compact set. Since the number of objects is not necessarily finite, we may not be able to arrange
the pairwise dissimilarities in a matrix and, instead, rely on the notion of a dissimilarity function.
Let M be a compact metric space, ∆(∞) : M × M → R≥0 be a dissimilarity function on M, and
h : M → Rd be a Borel-measurable embedding function. The continuous raw stress criterion [23]


                                                        2
```

## Page 3

```text
is defined by
                              Z    Z                                            2
         σ((∆(∞) , P), h) =                 ∥h(m′ ) − h(m′′ )∥ − ∆(∞) (m′ , m′′ ) P(dm′ )P(dm′′ ).
                               M    M

We let mds : M → Rd denote the embedding function that minimizes σ((∆(∞) , P), h) by varying
h over the set of all possible Borel-measurable embedding functions from M to Rd .
Remark 3. The function ∆     ˜ : M × M → R defined as ∆(m ˜    ′
                                                                 , m′′ ) = ∥h(m′ ) − h(m′′ )∥ is an
                                      d
Euclidean pseudometric on M to R . Since the set Y of all Euclidean pseudometrics from M
to Rd is closed and complete, σ((∆(∞) , P), h) can be minimized by varying h over the set of all
Borel-measurable embedding functions from M → Rd .

3     Description of the setting
A generative model is a random map from an input space or query space to an output space. Let
f1 , . . . fn be n generative models with the shared query space Q and the shared output space X ,
and suppose {q1 , . . . qm } is a collection of m queries. In our setting, every model fi responds to
every query qj exactly r times and we let fi (qj )k denote the k-th replicate of the response of fi to
qj . We assume that there exists an embedding function g that maps a response to a vector in Rs .
We let Fij denote the probability distribution of the vector-embedded responses of fi to qj , that is,
g(fi (qj )k ) ∼iid Fij for all i, j, k.
For every i, the model fi is represented by the matrix X̄i ∈ Rm×s whose j th rowPr is the mean over
replicates of the ith model’s response to the j th query, that is: (X̄i )j· = 1r k=1 g(fi (qj )k ) ≈
(µi )j· ≡ EFij [g(fi (qj )].
To capture the sample pairwise differences between the models, we define the matrix D ∈ Rn×n
                    1
with entries Dii′ = m  ||X̄i − X̄i′ ||F . Note that, for fixed n and m, as r → ∞, Dii′ converges to
                     1                                             n
the quantity ∆ii′ = m   ||µi − µi′ ||F . The matrix ∆ = (∆ii′ )i,i′ =1 is known as the model mean
discrepancy matrix.
Multidimensional scaling by raw stress minimization yields ψ    b = mds(D) ∈ Rn×d , representing our
collection of models as a configuration of n points in finite-dimensional Euclidean space Rd . The
geometry of ψb approximates the model discrepancy geometry configuration matrix ψ = mds(∆) ∈
  n×d
R     . We refer to the i-th row ψ i (respectively ψ
                                                   b ) of the matrix ψ (respectively ψ)
                                                     i
                                                                                     b as (our estimate
of) the data kernel perspective space (DKPS) representation of model fi with respect to the set of
queries {qj }. The remainder of this paper details the consistency of the estimated DKPS as n, m
and/or r grow.
Remark 4. In every setting we discuss, r → ∞. For quantities whose definition depends on r, such
as ψ,
   b we sometimes emphasize the dependence by writing ψ        b (r) .

4     Consistency of estimated model embeddings
The consistency results herein are presented in progressively more complicated settings where the
number of queries and/or the number of models grow with a growing number of replicates from each
Fij .

4.1   Fixed set of models and fixed set of queries
We start with the simplest setting where the number of models and the number of queries both
remain fixed and the number of replicates increases. In this setting, we can establish the consistency
of ψ
   b (up to an affine transformation) by direct use of Theorem 2 from [23], which establishes the
convergence guarantees for raw stress embeddings of a sequence of dissimilarity matrices of a fixed
size approaching another dissimilarity matrix.
Theorem 1. Let ψ    b ∈ MDS(D) ⊂ Rn×d . Then there exists a subsequence {ru }∞ of {r}∞ such
                                                                                  u=1        r=1
that for all pairs (i, i′ ) ∈ [n]2 ,
                                              
              b (ru ) − ψ
              ψ          b (r′ u ) − ∥ψ − ψ ′ ∥ →P 0 as u → ∞,
                i           i          i   i



                                                    3
```

## Page 4

```text
where ψ = [ψ 1 |ψ 2 | . . . |ψ n ]T ∈ MDS(∆) ⊂ Rn×d .
Theorem 1 states that by prompting each model with each query with enough replicates r, the
perspective space obtained via the raw stress criterion is close to the true-but-unknown perspective
space for the models with respect to {qj }.

4.2   Fixed set of models and growing set of queries
We next address the consistency of ψ   b in settings where the number of queries grows but the collection
of models is fixed. That is, n remains fixed but m → ∞ as r → ∞. Our results are adapted from
the results from [23], where they show that if a sequence of dissimilarity matrices of a fixed size
converges, then the raw stress embeddings of each term in the sequence approaches the raw stress
embeddings of the limiting dissimilarity matrix. While we could directly use this result to argue that
ψb approaches ψ for fixed n and m where Dii′ → ∆ii′ in Theorem 1, we cannot do so in the context
of growing m. In particular, as m increases, so too does the dimensionality of ∆. Hence, in order
to satisfy the condition that D approaches a specific dissimilarity matrix as m, r → ∞, we need an
additional assumption:
Assumption 1. For some q ∈ N, there exist vectors ϕ1 , . . . ϕn ∈ Rq , such that for every pair
(i, i′ ) ∈ [n]2 , ∆ii′ = m
                         1
                           ||µi − µi′ || → ∥ϕi − ϕi′ ∥ as r, m → ∞.
Assumption 1 presumes the existence of high-dimensional vector representations for each gener-
ative model. Our results will show that the sequence of low-dimensional raw stress configura-
tions converges to a low-dimensional approximation of the {ϕi } under appropriate conditions. Let
                        n
∆(∞) = {∥ϕi − ϕi′ ∥}i,i′ =1 ∈ Rn×n and ψ = mds(∆(∞) ) ∈ MDS(∆(∞) ) ⊂ Rn×d . Note that
the vectors ϕi being independent of m and r ensures that the dissimilarity matrices D approach a
specific limit ∆(∞) as m, r → ∞. Using results from [23], we show that if D approaches the model
mean discrepancy matrix ∆(∞) then ψ b approaches ψ.
Lemma 1. ([23]) Let ψ    b ∈ MDS(D) ⊂ Rn×d . Let n be fixed and let m grow with r. If
 D − ∆(∞)          →P 0 as r → ∞, then there exists a subsequence {ru }∞         ∞
                                                                       u=1 of {r}r=1 such that for
               F
all pairs (i, i′ ) ∈ [n]2 ,
                                                
                  (ru )     (ru )
              ψ i − ψ i′
               b         b        − ∥ψ i − ψ i′ ∥ →P 0 as u → ∞,

where ψ = [ψ 1 |ψ 2 | . . . |ψ n ]T ∈ MDS(∆(∞) ) ⊂ Rn×d .
We note that by the weak law of large numbers we have (X̄i )j· →P (µi )j· as r → ∞. However, if
m is large while r is relatively small, then there is non-zero probability that many rows in X̄i are
far away from the corresponding rows in µi . Thus, if m grows too fast with respect to r, D may
not approach ∆(∞) and the condition of Lemma 1 will not be met. We next establish a sufficient
condition for the rate at which m can grow with respect to r for the condition of Lemma 1.
Theorem 2. Let Σij = cov[g(fi (qj )k )] be the covariance matrix associated with the distribution
Fij and γij = trace(Σij ). If, for all i ∈ [n],
                1
                  Pm
                m    j=1 γij
          lim                =0
         r→∞         r
then D − ∆(∞)            →P 0 as r → ∞.
                     F

AsP  a consequence of Lemma 1 and Theorem 2, a sufficient condition for consistency of ψ         b is
 1      m
 m      j=1 γ ij  =  o(r) for  all i ∈ [n].
                                                                           1
                                                                              Pm
Theorem 3. In the setting of Theorem 2, suppose for all i ∈ [n], m              j=1 γij = o(r). Also,
let ψ ∈ MDS(D) ⊂ R
     b                          n×d
                                     . There exists a subsequence {ru }u=1 of {r}∞
                                                                       ∞
                                                                                 r=1 such that for all
(i, i′ ) ∈ [n]2 ,
                                                   
                   (ru )     (ru )
                ψ i − ψ i′
                 b         b         − ∥ψ i − ψ i′ ∥ →P 0 as u → ∞,

where ψ = [ψ 1 |ψ 2 | . . . |ψ n ]T ∈ MDS(∆(∞) ) ⊂ Rn×d .


                                                   4
```

## Page 5

```text
Thus, Theorem 3 gives us an idea of how fast m can grow with respect to r as a function of Fij , in
order for ψb to be consistent. Observe that if maxj∈[m] γij = O(1) for all i ∈ [n], then m can grow
arbitrarily fast with respect to r, and ψ
                                        b will still be consistent.

As a consequence of Theorem 3, each ψ    b will accumulate to some affine transformation of ψ , which
                                          i                                                   i
is stated in the following corollary.
                                                                       1
                                                                         Pm
Corollary 1. In the setting of Theorem 3, suppose for all i ∈ [n], m       j=1 γij = o(r). Then there
                    (u) ∞           (u) ∞                    (u)
exist sequences W          u=1
                                and   a     u=1
                                                , satisfying W     ∈ O(d) and a(u) ∈ Rd for all u ∈ N,
such that for all i ∈ [n],
            b (ru ) − W(u) ψ + a(u) →P 0 as u → ∞.
                                       
            ψ i                i


Corollary 1 states that there is a subsequence of minimizers of the raw stress criterion that is close to
the true-but-unknown perspectives as the number of queries and number of replicates for each query
grow. In our set up the true-but-unknown perspective space depends on the collection of models
and the growing set of queries. While our results allow for arbitrary growing sets of queries, the
true-but-unknown perspective space is most easily characterized when the queries come from an
explicit query distribution.

4.3   Growing set of models and growing set of queries
We now let both the number of models and the number of queries grow as the number of replicates
grow and establish that under appropriate conditions ψ  b is consistent. In this setting, we need an
adaptation of Assumption 1 that further assumes that the vectors that induce the limiting dissimilarity
are elements of a compact Riemannian manifold:
Assumption 2. Let M be a compact Riemannian manifold. For every model fi , there exists a vector
ϕi ∈ M ⊂ Rq , such that for all pairs (i, i′ ) ∈ N × N, m
                                                        1
                                                          ∥µi − µi′ ∥ → ∥ϕi − ϕi′ ∥ as r → ∞.
Recall that in the growing sample size scenario, the definition of raw stress relies on a dissimilarity
function. In our setting, we define the following dissimilarity function ∆(∞) : M × M → R≥0 to
be ∆(∞) (ϕi , ϕi′ ) = ∥ϕi − ϕi′ ∥. Results from [23] tell us that ψb is consistent if Dii′ approaches
  (∞)                           ′
∆ (ϕi , ϕi′ ) for all pairs i, i ∈ [n].
Lemma 2. ([23]) Let ϕi ∼iid P. Assume that for all pairs (i, i′ ) ∈ N × N, Dii′ →P ∆(∞) (ϕi , ϕi′ )
as r → ∞. Then, for some subsequence {ru }∞           ∞
                                          u=1 of {r}r=1 , for all p ≥ 1,
        Z Z                                                      p
                      (ru )   (ru )
                   ψ1 − ψ2
                    b       b       − ∥mds(ϕ1 ) − mds(ϕ2 )∥
           M   M
                                 P(dϕ1 )P(dϕ2 ) →P 0 as u → ∞.

The above theorem establishes that if the pairwise distances Dii′ approach the dissimilarities
∆(∞) (ϕi , ϕi′ ), then ψ̂ is consistent. In order for Dii′ to approach ∆(∞) (ϕi , ϕi′ ), a result sim-
ilar to Theorem 2 is needed, which holds in the regime of growing n. Such a result can be shown to
hold true by the same equipment used to establish Theorem 2.
Theorem 4. In our setting where m, n → ∞ as r → ∞, |Dii′ − ∆(∞) (ϕi , ϕi′ )| →P 0 for every
pair (i, i′ ) ∈ N × N, if
                 1
                   Pm
                 m   j=1 γij
            lim              = 0 for all i.
           r→∞        r
It may seem a bit surprising at first that the sufficient conditions in both scenarios are the same: The
setting with growing m and n was expected to be more restrictive. Note that in both cases (of fixed n
and growing n), it is pointwise convergenceP    of Dii′ to ∆(∞) (ϕi , ϕi′ ) that we need. That is why in
                                             1    m
each of the cases it suffices to ensure that m j=1 γij = o(r) for all i. Further, the condition that for
      1
        P  m
all i m    j=1 γij = o(r) is more difficult to ensure when n grows than when n is fixed.

As in Section 4.2, the lemmas in this section allow us to deduce a sufficient condition for the
consistency of ψ:
               b


                                                   5
```

## Page 6

```text
                           Language models                                                        Text-to-image models
                         (LLaMA-3-8B-Instruct)                                                (StableDiffusion-3.5-medium)
                                         Average || *i W (r)
                                                          i ||2                                                    Average || *i W (r)
                                                                                                                                   i ||2
               * (n=10, m=20, r=50)            for each i                               * (n=20, m=100, r=25)           for each i
         1.0                      r=1                                                                    r=1 0.20
         0.5                      r=5 0.15                                        0.4                    r=5 0.15
DKPS 2




                                                                         DKPS 2
                                  r=20 0.10                                       0.2                    r=10
         0.0                                                                                                   0.10
                                       0.05                                       0.0                          0.05
         0.5                                                                      0.2                          0.00
                 1.0 0.5 0.0 0.5 1.0          12 5      10          20                   0.2 0.0 0.2 0.4 0.6          12 5   10             25
                      DKPS 1                  Number of replicates (r)                         DKPS 1                 Number of replicates (r)

Figure 1: Numerical evidence of the consistency of ψ b to ψ for fixed n and fixed m for a collection of
language models (left) and a collection of text-to-image models (right). The black dots in the left
figure of each pair are the 2-d perspectives of models induced with randomly selected queries, R
replicates each, and a domain-specific embedding function. The red circles have radius equal to the
average L2 between ψb∗ and model representations estimated with r replicates for each query. The
right figure of each pair shows the distribution of the average L2 norm in the DKPS across models
for various r. More replicates improves estimation quality.
                                                                    1
                                                                      Pm
Theorem 5. In the setting of Lemma 2, suppose for all i ∈ N, m          j=1 γij = o(r). Then, for all
p ≥ 1, for some subsequence {ru }∞   u=1 of {r}∞
                                               r=1 ,
          Z Z                                                     p
                        (ru )    (ru )
                      ψ1 − ψ2
                      b        b       − ∥mds(ϕ1 ) − mds(ϕ2 )∥ P(dϕ1 )P(dϕ2 ) →P 0 as u → ∞.
                  M     M

Thus, even in the case where n grows, m is allowed to grow arbitrarily fast with respect to r if
maxj∈[m] γij = O(1) for all i. Moreover, since all we need is pointwise convergence of D to ∆(∞) ,
n can grow arbitrarily fast with respect to r.

5        Numerical experiments
We next provide empirical support of the consistency of the representations of models in the three
settings we analyzed above. For each setting, we study a collection of large language models and a
collection of text-to image models.

Language models
For our language model example, we study collections of different LLaMA-3-8B-Chat [8] models.
The models are parameterized by different fixed context augmentations ai , i.e., fi = f ( · ; ai ). Each
ai is a text string related to RA Fisher such as ai = “RA Fisher pioneered the principles of the
design of experiments.” or ai′ = “RA Fisher’s view on eugenics were primarily based on anecdotes
and prejudice." written by us. Given a query qj , the base model is prompted with the appropriately
formatted prompt “ai qj ” R = 50 times. In our experiments we consider up to 174 questions about
RA Fisher such as qj = “What is R.A. Fisher’s most well-known statistical theorem?" as queries.
We consider up to N = 50 models. The questions were sampled from ChatGPT with the prompt
“Provide 200 questions related to RA Fisher". We did not include a random 26 questions. We use
the open source embedding model nomic-embed-text-v1.5 [18] to construct X̄i ∈ Rm×756 and
GrasPy’s [6] implementation of multi-dimensional scaling to map the collection of X̄i to R2 .

Text-to-image models
For our text-to-image example, we study collections of StableDiffusion-3.5-medium [10]. As
with our language model example, we parameterize different models by different fixed context
augmentations. Each fixed augmentation ai is an instruction to produce an image in the style of a
famous artist – for example, ai = “in the style of Pablo Picasso" or ai′ = “in the style of Leonardo
da Vinci" – and fi = f ( · ; ai ). We consider up to N = 100 models. Given a query qj , the
base model is prompted with the appropriately formatted prompt “qj ai ” R = 25 times. Each
query qj is an instruction to produce an image of a noun. For example, one of the prompts for the
model corresponding to da Vinci is “An apple in the style of Leonardo da Vinci". The nouns were
generated from ChatGPT with the prompt “Provide 500 nouns." We use the open source embedding
model nomic-embed-vision-v1.5 to map the generated images to a vector space and construct


                                                                         6
```

## Page 7

```text
                           Language models                                                                Text-to-image models
                         (LLaMA-3-8B-Instruct)                                                        (StableDiffusion-3.5-medium)
                                                                                                * (n=20, m=500, r=25)
                                                                                                                       0.4 Average ||              W||2,
               * (n=10, m=174, r=50)    Average || *               W||2,                                                              *
                   (m,r)=(10, 5)          0.4                        r=1                  0.4                (m,r)=(50, 5)                              r=1
         0.4       (m,r)=(20, 10)                                    r=5                                     (m,r)=(100, 10) 0.3                        r=5
                   (m,r)=(50, 20)         0.3                        r=50                                    (m,r)=(200, 25)                            r=25




                                                                                 DKPS 2
DKPS 2
                                                                                          0.2                               0.2
         0.0                              0.2
                                                                                          0.0                               0.1
                                          0.1
         0.4 0.5                                                                                 0.2   0.0    0.2    0.4    0.0 1         10      100
                          0.0       0.5         1            10        100
                       DKPS 1                       Number of queries (m)                               DKPS 1                      Number of queries (m)

Figure 2: Numerical evidence of the consistency of ψ     b to ψ for fixed n and growing m. The black
dots in the left of each pair of figures are the 2-d perspectives of n models induced with M queries
and R replicates each. The red circles have radius equal to the average L2 norm between the “ground
truth" and model representations estimated for selected (m, r) pairs. The right figures show the
average maximum row L2 norm for various (m, r) pairs. More replicates and more queries improves
estimation quality. The number of queries appears to have a larger effect.

the X̄i ∈ Rm×768 . We again use GrasPy’s implementation of multi-dimensional scaling to induce
the data kernel perspective space of the models. To avoid sounding repetitive, we use N , M , and
R to mean the maximum number of models, queries, and replicates for both the language model
experiments and the text-to-image experiments. For the language model experiment, N = 50,
M = 174, and R = 50. For the text-to-image experiment, N = 100, M = 500, and R = 25.
For both sets of experiments we do not have the “ground truth" DKPS ψ in any parameter setting,
and thus treat ψ
               b estimated with r = R as a proxy for the ground truth. For settings with growing n
and/or growing m, we similarly treat ψb (R) estimated with n = N and m = M as the ground truth.
                                 ∗
                               b . We let d = 2 in all settings for visualization purposes. Finally, in
We refer to these estimates as ψ
settings where n, m, or r grow, we sample from the appropriate set of models, queries, or replicates
with replacement to calculate ψb and report the average L2 norm or average two-to-infinity norm of
                          ∗
the difference between ψ b and ψW b of 10 bootstrap samples, where W ∈ O(2) is the Procrustes
solution [12].

5.1        Fixed collection of models and fixed set of queries
As with the theoretical analysis, our empirical analysis starts in the simplest setting where n and m
are fixed while r grows. The collection of models and set of queries were selected at random without
replacement – n = 10 and m = 20 for the language model example, n = 20 and m = 100 for the
text-to-image example. The target DKPS ψ     b∗ for the two experiments are shown on the left for each
pair of figures of Figure 1. Each black dot represents a model. The red circles have radius equal to the
average (across bootstrap samples) L2 norm between ψ     b∗ and ψ
                                                                b(r) W for selected r. The right figure
for each pair of figures of Figure 1 shows the distribution of the average (across bootstrap samples)
L2 norm for each model for more values of r. The decreasing average L2 norm for all models as r
increases supports Theorem 1.

5.2        Fixed collection of models and growing set of queries
We next consider the setting where n is fixed and both m and r grow. We use the same models as
above. The two target DKPS ψ b ∗ are shown on the left for each pair of Figure 2. They were estimated
with m = M and r = R. As with Figure 1, the red circles have radius equal to the average (across
bootstrap samples) L2 norm of the difference between ψ   b ∗ and ψW
                                                                  b     for selected (m, r) pairs. The
right figure of Figure 2 shows the average two-to-infinity norm of the difference between ψ    b ∗ and
ψb across bootstrap samples for more values of (m, r). The two-to-infinity norm decreases as both
(m, r) increase, which supports Theorem 3.
The right figure of each pair figures of Figure 2 shows the possibility of a computational trade-off
between increasing m and increasing r. In particular, the computational cost of each iteration of
the experiment is approximately O(mr): getting more replicates of a fixed number of queries is
approximately the same as getting a small set of replicates for more queries from a compute stand


                                                                             7
```

## Page 8

```text
                           Language models                         Text-to-image models
                         (LLaMA-3-8b-Instruct)                 (StableDiffusion-3.5-medium)
                              Average || *       W ||2,                  Average || *    W ||2,
                   0.4                       (m,r)=(1, 1)                            (m,r)=(1, 1)
                                             (m,r)=(50, 1)                           (m,r)=(20, 5)
                   0.3                       (m,r)=(50, 10)        0.3               (m,r)=(500, 25)
                                             (m,r)=(100, 50)
                   0.2
                                                                   0.2
                   0.1
                                                                   0.1
                         10      20    30         40      50             20   40    60     80     100
                               Number of models (n)                       Number of models (n)

Figure 3: Numerical evidence of the consistency of ψ
                                                   b to ψ for growing n and growing m. The two
target DKPS ψb were estimated using N , M , and R.

point. From an estimation stand point, however, the right figures of Figure 2 shows that getting
more queries may be more beneficial. Per Theorem 2, this observation depends on the distributional
properties of each Fij .

5.3   Growing collection of models and growing set of queries

Finally, we consider the setting with growing n and growing m. The two target DKPS ψ       b ∗ were
estimated using all N models, all M queries and all R replicates per query. For each (n, m, r) triple,
we randomly sample n models, m queries, and r replicates with replacement and estimate the DKPS
ψ.
b Figure 3 shows the average two-to-infinity norm of the difference between ψ    b ∗ and ψW
                                                                                         b    across
bootstrap samples for the n sampled models. As each element of the triple increases, the reported
difference gets close to 0, which supports Theorem 5.
Similar to the difference in the effect on estimation between r and m, we observe a similar difference
in the effect of estimation between r and n in Figure 3. In particular, increasing the number of models
appears to have a larger effect on estimation than increasing r (or, even increasing m). As above, this
observation depends on the Fij , per Theorem 4. Unlike the observation in Figure 2, however, the
computational cost of increasing n is larger than increasing m or r since m · r samples from Fij are
required for each additional n. Thus, there is a more delicate trade-off between computational cost
and estimation quality in this setting than in the fixed n case.


6     Discussion
In [13], a novel method was proposed for embedding generative models into a finite-dimensional
Euclidean space in the context of queries – the data kernel perspective space. In this paper, we
analyzed the estimated perspective space in regimes where the number of models and/or the number
of queries can remain fixed or grow and demonstrated that it is consistent for a population-level
perspective space. Importantly, we also describe sufficient conditions for consistent estimation of
the perspective space. In this regard, we establish that if the number of queries and/or models grow
adequately slowly with the number of replicates relative to distributional properties of the Fij then
the perspective space can be estimated consistently.
Low-dimensional representations of collections of generative models enable the use of classical
methods to understand differences in model behavior and, eventually, to make sense of model
evolution. For example, [13] uses the perspective space to demonstrate that the communication
structure underlying a system of interacting language models has an impact on system-level and
model-level dynamics. Going further, the perspective space can be used for model-level inference
problems such as predicting the the pre-training data mixture, predicting model safety, predicting the
model’s score on a benchmark, etc. Deeper investigations into these applications are warranted and
our results support the perspective space as a principled foundation for these pursuits.
While the consistency of the estimated perspective space holds for all choices of the dimensionality
of the raw stress embeddings, we note that the choice will impact practical properties of the estimate.
In particular, choosing large d may result in slower convergence. Conversely, choosing small d may


                                                               8
```

## Page 9

```text
result in fast convergence but to a limiting set of vectors that poorly approximate the high-dimensional
{ϕi }.
Further, the consistency of the estimated perspectives is the least we could ask for [2]. We expect
concentration inequalities and distributional results for the estimated perspectives to be important
theoretical extensions to support applications in non-asymptotic regimes. For example, establishing
uniform convergence of the perspectives would enable use of the estimated perspective space as a
principled substitute for its population counterpart after a particular amount of models, queries, and
replicates. Similarly, establishing distributional properties of the estimated perspectives, such as
asymptotic normality, in particular settings as to practicable inference methods.
We required Assumptions 1 and 2 to establish consistency of ψ     b in regimes for growing m with
either fixed or growing n. In particular, we assume the existence of a collection of vectors in a finite
and fixed q-dimensional Euclidean space whose inner point distances are the limiting dissimilarities
between the perspectives. These two assumptions put implicit constraints on how the queries grow
and on the properties of each Fij . An important and more general follow-on investigation may relax
this assumption such that {ϕi } exist in a reproducing kernel Hilbert space.
We note that for most generative models in practice such as large language models with a maximum
context size and maximum output sequence length and diffusion models that output RBG images,
there are only a finite many possible input and output sequences or images. Hence, the maximum
trace of the covariance matrices of {Fij } does not grow without bound and, importantly, we are in
the regime where m or n can grow arbitrarily fast with respect to r.
Lastly, our results are for representations of models in the context of a set of queries. There are
other potential vector representations of models that do not depend on a set of queries, such as
model weights. The geometry of these quantities can similarly be obtained in settings where an
appropriate dissimilarity is defined. In our setting, different sets of queries will approximate the
non-query dependent geometry to different degrees. Investigations into how well different query
sets approximate more inherent features of the models are necessary, as well as investigations into
practical trade-offs between query-independent and query-dependent model representations.

Acknowledgements.
We would like to thank Avanti Athreya, Brandon Duderstadt, Youngser Park, and Zekun Wang for
helpful discussions and comments throughout the development of this manuscript.




                                                   9
```

## Page 10

```text
References
 [1] Sercan Ö Arık, Mike Chrzanowski, Adam Coates, Gregory Diamos, Andrew Gibiansky, Yong-
     guo Kang, Xian Li, John Miller, Andrew Ng, Jonathan Raiman, et al. Deep voice: Real-time
     neural text-to-speech. In International conference on machine learning, pp. 195–204. PMLR,
     2017.

 [2] Peter J Bickel and Kjell A Doksum. Mathematical statistics: basic ideas and selected topics,
     volumes I-II package. Chapman and Hall/CRC, 2015.

 [3] Ingwer Borg and Patrick JF Groenen. Modern multidimensional scaling: Theory and applica-
     tions. Springer Science & Business Media, 2005.

 [4] Tom Brown, Benjamin Mann, Nick Ryder, Melanie Subbiah, Jared D Kaplan, Prafulla Dhariwal,
     Arvind Neelakantan, Pranav Shyam, Girish Sastry, Amanda Askell, et al. Language models are
     few-shot learners. Advances in neural information processing systems, 33:1877–1901, 2020.

 [5] Guodong Chen, Hayden S Helm, Kate Lytvynets, Weiwei Yang, and Carey E Priebe. Mental
     state classification using multi-graph features. Frontiers in Human Neuroscience, 16:930291,
     2022.

 [6] Jaewon Chung, Benjamin D. Pedigo, Eric W. Bridgeford, Bijan K. Varjavand, Hayden S. Helm,
     and Joshua T. Vogelstein. Graspy: Graph statistics in python. Journal of Machine Learning
     Research, 20(158):1–7, 2019. URL http://jmlr.org/papers/v20/19-490.html.

 [7] Katherine Crowson, Stella Biderman, Daniel Kornis, Dashiell Stander, Eric Hallahan, Louis
     Castricato, and Edward Raff. Vqgan-clip: Open domain image generation and editing with
     natural language guidance. In European Conference on Computer Vision, pp. 88–105. Springer,
     2022.

 [8] Abhimanyu Dubey, Abhinav Jauhri, Abhinav Pandey, Abhishek Kadian, Ahmad Al-Dahle,
     Aiesha Letman, Akhil Mathur, Alan Schelten, Amy Yang, Angela Fan, et al. The llama 3 herd
     of models. arXiv preprint arXiv:2407.21783, 2024.

 [9] Brandon Duderstadt, Hayden S. Helm, and Carey E. Priebe. Comparing foundation models
     using data kernels, 2024. URL https://arxiv.org/abs/2305.05126.

[10] Patrick Esser, Sumith Kulal, Andreas Blattmann, Rahim Entezari, Jonas Müller, Harry Saini,
     Yam Levi, Dominik Lorenz, Axel Sauer, Frederic Boesel, et al. Scaling rectified flow transform-
     ers for high-resolution image synthesis. In Forty-first International Conference on Machine
     Learning, 2024.

[11] Guglielmo Faggioli, Laura Dietz, Charles LA Clarke, Gianluca Demartini, Matthias Hagen,
     Claudia Hauff, Noriko Kando, Evangelos Kanoulas, Martin Potthast, Benno Stein, et al. Per-
     spectives on large language models for relevance judgment. In Proceedings of the 2023 ACM
     SIGIR International Conference on Theory of Information Retrieval, pp. 39–50, 2023.

[12] Colin Goodall. Procrustes methods in the statistical analysis of shape. Journal of the Royal
     Statistical Society: Series B (Methodological), 53(2):285–321, 1991.

[13] Hayden Helm, Brandon Duderstadt, Youngser Park, and Carey E Priebe. Tracking the perspec-
     tives of interacting language models. arXiv preprint arXiv:2406.11938, 2024.

[14] Hayden S Helm, Weiwei Yang, Sujeeth Bharadwaj, Kate Lytvynets, Oriana Riva, Christopher
     White, Ali Geisa, and Carey E Priebe. Inducing a hierarchy for multi-class classification
     problems. arXiv preprint arXiv:2102.10263, 2021.

[15] Joseph B Kruskal. Multidimensional scaling by optimizing goodness of fit to a nonmetric
     hypothesis. Psychometrika, 29(1):1–27, 1964.

[16] Tomas Mikolov. Efficient estimation of word representations in vector space. arXiv preprint
     arXiv:1301.3781, 2013.


                                                10
```

## Page 11

```text
[17] Arvind Neelakantan, Tao Xu, Raul Puri, Alec Radford, Jesse Michael Han, Jerry Tworek,
     Qiming Yuan, Nikolas Tezak, Jong Wook Kim, Chris Hallacy, et al. Text and code embeddings
     by contrastive pre-training. arXiv preprint arXiv:2201.10005, 2022.
[18] Zach Nussbaum, John X. Morris, Brandon Duderstadt, and Andriy Mulyar. Nomic embed:
     Training a reproducible long context text embedder, 2024. URL https://arxiv.org/abs/
     2402.01613.
[19] Rajvardhan Patil, Sorio Boit, Venkat Gudivada, and Jagadeesh Nandigam. A survey of text
     representation and embedding techniques in nlp. IEEE Access, 11:36120–36146, 2023. doi:
     10.1109/ACCESS.2023.3266377.
[20] N Reimers. Sentence-bert: Sentence embeddings using siamese bert-networks. arXiv preprint
     arXiv:1908.10084, 2019.
[21] Victor Sanh, Albert Webson, Colin Raffel, Stephen H Bach, Lintang Sutawika, Zaid Alyafeai,
     Antoine Chaffin, Arnaud Stiegler, Teven Le Scao, Arun Raja, et al. Multitask prompted training
     enables zero-shot task generalization. arXiv preprint arXiv:2110.08207, 2021.
[22] Uriel Singer, Adam Polyak, Thomas Hayes, Xi Yin, Jie An, Songyang Zhang, Qiyuan Hu,
     Harry Yang, Oron Ashual, Oran Gafni, et al. Make-a-video: Text-to-video generation without
     text-video data. arXiv preprint arXiv:2209.14792, 2022.
[23] Michael W Trosset and Carey E Priebe. Continuous multidimensional scaling. arXiv preprint
     arXiv:2402.04436, 2024.
[24] Nian Wang, Robert J. Anderson, David G. Ashbrook, Vivek Gopalakrishnan, Youngser Park,
     Carey E. Priebe, Yi Qi, Rick Laoprasert, Joshua T. Vogelstein, Robert W. Williams, and G. Allan
     Johnson. Variability and heritability of mouse brain structure: Microscopic mri atlases and
     connectomes for diverse strains. NeuroImage, 222:117274, 2020. ISSN 1053-8119. doi:
     https://doi.org/10.1016/j.neuroimage.2020.117274.
[25] Shun Zhang, Zhenfang Chen, Yikang Shen, Mingyu Ding, Joshua B Tenenbaum, and
     Chuang Gan. Planning with large language models for code generation. arXiv preprint
     arXiv:2303.05510, 2023.




                                                11
```

## Page 12

```text
A     Proofs of lemmas and theorems
A.1   Fixed set of models and fixed set of queries

Theorem 1. Let ψ    b ∈ MDS(D) ⊂ Rn×d . Then there exists a subsequence {ru }∞ of {r}∞ such
                                                                             u=1     r=1
that for all pairs (i, i′ ) ∈ [n]2 ,
                                           
               (ru )   (ru )
             ψ i − ψ i′
             b       b       − ∥ψ i − ψ i′ ∥ →P 0 as u → ∞,


where ψ = [ψ 1 |ψ 2 | . . . |ψ n ]T ∈ MDS(∆) ⊂ Rn×d .

Proof. See Theorem 2 of [23].

A.2   Fixed set of models and growing set of queries

             b ∈ MDS(D) ⊂ Rn×d . Let n be fixed and let m grow with r. If D − ∆(∞)
Lemma 1. Let ψ                                                                                  →0
                                                                                             F
as r → ∞, then there exists a subsequence {ru }∞         ∞                                ′       2
                                               u=1 of {r}r=1 such that for all pairs (i, i ) ∈ [n] ,

                                           
               (ru )   (ru )
             ψ i − ψ i′
             b       b       − ∥ψ i − ψ i′ ∥ → 0 as u → ∞,


where ψ = [ψ 1 |ψ 2 | . . . |ψ n ]T ∈ MDS(∆(∞) ) ⊂ Rn×d .
Proof. See Theorem 2 of [23].


Theorem 2. Let Σij = cov[g(fi (qj )k )] be the covariance matrix associated with the distri-
bution Fij and γij = trace(Σij ). If, for all i ∈ [n],

                1
                    Pm
                m     j=1 γij
         lim                    =0
         r→∞          r

then D − ∆(∞)        →P 0 as r → ∞.
                  F
Proof. Observe that by triangle inequality,

          X̄i − X̄i′ F ≤ (X̄i − µi ) − (X̄i′ − µi′ ) F + ∥µi − µi′ ∥F
          =⇒        X̄i − X̄i′ F − ∥µi − µi′ ∥F ≤ X̄i − µi F + X̄i′ − µi′ F .

Similarly, we obtain,

         ∥µi′ − µi ∥F ≤ (X̄i − µi ) − (X̄i′ − µi′ ) F + X̄i′ − X̄i F
          =⇒ ∥µi′ − µi ∥F − X̄i′ − X̄i F ≤ X̄i − µi F + X̄i′ − µi′ F .

Thus, from the above two equations combined, we get,

             X̄i − X̄i′ F − ∥µi − µi′ ∥F ≤ X̄i − µi F + X̄i′ − µi′ F .                           (2)


From eqn (1),

                            1              1
         |Dii′ − ∆ii′ | ≤     X̄i − µi F +   X̄i′ − µi′ F .                                      (3)
                            m              m

                                                12
```

## Page 13

```text
                                                                          1
Eqn (2) tells us that, in order to get ∥D − ∆∥F →P 0, it suffices to have m X̄i − µi F →P 0 for
all i ∈ [n]. Now, for an arbitrary ϵ,
                                    
               1
          P       X̄i − µi F > ϵ
               m
                                                  
                  m
                 X                        2
           ≤ P         (X̄i )j· − (µi )j· > m2 ϵ2 
                     j=1
                                                         
                     m n                                 o
                     [                             2
           ≤ P                  (X̄i )j· − (µi )j· > mϵ2 
                     j=1
               m         h                                    i
               X                                  2
           ≤         P       (X̄i )j· − (µi )j·       > mϵ2
               j=1
              m                        2
             X    E (X̄i )j· − (µi )j·
           ≤                             .
             j=1
                          mϵ2
                         Pr
Recall that (X̄i )j· = 1r k=1 Xijk where Xijk ∼iid Fij and the distribution Fij has mean (µi )j·
and covariance matrix Σij . Thus, E[(X̄i )j· ] = (µi )j· and cov[(X̄i )j· ] = 1r Σij . Hence,
                                                                          
                               2                                   1             γij
         E (X̄i )j· − (µi )j· = trace(cov[(X̄i )j· ]) = trace        Σij =
                                                                   r              r
where γij = trace(Σij ). Hence,
                                   m                       2   Pm
                                      E (X̄i )j· − (µi )j·      j=1 γij
                                X
            1
        P       X̄i − µi F > ϵ ≤                  2
                                                             ≤          .
            m                     j=1
                                              mϵ                rmϵ2
                                       1
Recall that as r → ∞, ∥D − ∆∥F →P 0 if m X̄i − µi F →P 0 for all i ∈ [n].
                     1
                         Pm
                             j=1 γij
Thus, limr→∞ m               r         = 0 for all i ∈ [n] ensures that ∥D − ∆∥ →P 0, which again implies
(using Assumption 1 and Triangle Inequality) D − ∆(∞) →P 0 as r → ∞.

                                                                            1
                                                                              Pm
Theorem 3.            In the setting of Theorem 2, suppose for all i ∈ [n], m    j=1 γij = o(r).
Also, let ψ b ∈ MDS(D) ⊂ Rn×d . There exists a subsequence {ru }∞ of {r}∞ such that for all
                                                                    u=1      r=1
(i, i′ ) ∈ [n]2 ,
                                                
                  (ru )     (ru )
                ψ i − ψ i′
                b         b       − ∥ψ i − ψ i′ ∥ →P 0 as u → ∞,

where ψ = [ψ 1 |ψ 2 | . . . |ψ n ]T ∈ MDS(∆(∞) ) ⊂ Rn×d .
                        1
                            Pm                                                        (∞)
Proof. Let us assume m         j=1 γij = o(r). From Theorem 2, then we must have D − ∆                 →P
                                                                                                   F
0 as r → ∞. From Lemma 1, this means there exists a subsequence {ru }∞         ∞
                                                                     u=1 of {r}r=1 such that for
               ′       2
all pairs (i, i ) ∈ [n] ,
                                               
                 (ru )     (ru )
               ψ i − ψ i′
               b         b       − ∥ψ i − ψ i′ ∥ →P 0

as u → ∞.

A.3   Growing set of models and growing set of queries
Lemma 2. Let ϕi ∼iid P. Assume that for all pairs (i, i′ ) ∈ N × N, Dii′ →P ∆(∞) (ϕi , ϕi′ ) as
r → ∞. Then, for some subsequence {ru }∞          ∞
                                        u=1 of {r}r=1 , for all p ≥ 1,
    Z Z                                                   p
                b (ru ) − ψ
                ψ         b (ru ) − ∥mds(ϕ ) − mds(ϕ )∥ P(dϕ )P(dϕ ) →P 0 as u → ∞.
                  1         2             1            2             1    2
       M    M


                                                                  13
```

## Page 14

```text
Proof. See Theorem 3 of [23].


Theorem 4. In our setting where m, n → ∞ as r → ∞, |Dii′ − ∆(∞) (ϕi , ϕi′ )| →P 0
for every pair (i, i′ ) ∈ N × N, if
                1
                   Pm
                m       j=1 γij
          lim                   = 0 for all i.
         r→∞            r
                                                                     1                 1
Proof. Recall (from the proof of Theorem 2) that |Dii′ − ∆ii′ | ≤ m      X̄i − µi F + m  X̄i′ − µi′ F
                                               P m                                       1
                                                                                           Pm
                      1                        j=1 γ ij                                       γij
and that for all i, P m X̄i − µi F > ϵ ≤ rmϵ         2    for any ϵ > 0. Thus, if limr→∞ m j=1r     =
                    1
0 for all i, then m     X̄i − µi →P 0 for all i, which in turn implies |Dii′ − ∆ii′ | →P 0 for all
pairs (i, i′ ) ∈ N2 as r → ∞. Using Assumption 2 and Triangle Inequality, we have that for all pairs
(i, i′ ) ∈ N2 , |Dii′ − ∆(∞) (ϕi , ϕi′ )| →P 0 as r → ∞. Using Lemma 2, for all p ≥ 1, for some
subsequence {ru }∞               ∞
                     u=1 of {r}r=1 ,
         Z Z                                                     p
                     b (ru ) − ψ
                     ψ         b (ru ) − ∥mds(ϕ ) − mds(ϕ )∥ P(dϕ )P(dϕ ) →P 0 as u → ∞.
                       1         2             1              2            1        2
       M    M




                                                                      1
                                                                        Pm
Theorem 5.         In the setting of Lemma 2, suppose for all i ∈ N, m     j=1 γij = o(r).
Then, for all p ≥ 1, for some subsequence {ru }∞
                                               u=1 of {r} ∞
                                                          r=1 ,
      Z Z                                                  p
                     (ru )    (ru )
                  ψ1 − ψ2
                  b         b       − ∥mds(ϕ1 ) − mds(ϕ2 )∥ P(dϕ1 )P(dϕ2 ) →P 0 as u → ∞.
       M    M
                                Pm
                          1
Proof. Let us assume that m       j=1 γij   = o(r). Then, by Theorem 4, for all pairs (i, i′ ) ∈ N2 ,
|Dii′ − ∆(∞) (ϕi , ϕi′ )| →P 0 as r → ∞. Using Lemma 2, for some subsequence {ru }∞ u=1 of
{r}∞
   r=1 , for all p ≥ 1,
      Z Z                                                 p
                      (ru )   (ru )
                   ψ1 − ψ2
                    b       b       − ∥mds(ϕ1 ) − mds(ϕ2 )∥ P(dϕ1 )P(dϕ2 ) →P 0 as u → ∞.
       M    M
.




                                                  14
```
