# Concentration bounds on response-based vector embeddings of black-box generative models

**Authors:** Aranyak Acharyya, Joshua Agterberg, Youngser Park, Carey E. Priebe
**arXiv:** 2511.08307v1
**Date:** submitted 2025-11-11
**Source:** https://arxiv.org/abs/2511.08307

**Transcription note:** Foundational DKPS concentration paper. This is the paper whose concentration theorem is closest to the load-bearing hypothesis imported by downstream DKPS formalizations.

This file is an automatically generated Markdown transcription from the arXiv PDF using `pdftotext -layout`. It preserves page breaks and much of the equation/table layout as plaintext. For formal proof work, verify theorem statements and proof-critical equations against the PDF or TeX source.

## Page 1

```text
                                           Concentration bounds on response-based vector embeddings of
                                                           black-box generative models
                                                   Aranyak Acharyya, Joshua Agterberg, Youngser Park, Carey E. Priebe
                                                                                     November 12, 2025

                                                                                            Abstract
                                                     Generative models, such as large language models or text-to-image diffusion models, can gen-
                                                 erate relevant responses to user-given queries. Response-based vector embeddings of generative
                                                 models facilitate statistical analysis and inference on a given collection of black-box generative
                                                 models. The Data Kernel Perspective Space embedding is one particular method of obtaining
                                                 response-based vector embeddings for a given set of generative models, already discussed in the
                                                 literature. In this paper, under appropriate regularity conditions, we establish high probability
arXiv:2511.08307v1 [stat.ML] 11 Nov 2025




                                                 concentration bounds on the sample vector embeddings for a given set of generative models,
                                                 obtained through the method of Data Kernel Perspective Space embedding. Our results tell us
                                                 the required number of sample responses needed in order to approximate the population-level
                                                 vector embeddings with a desired level of accuracy. The algebraic tools used to establish our
                                                 results can be used further for establishing concentration bounds on Classical Multidimensional
                                                 Scaling embeddings in general, when the dissimilarities are observed with noise.
                                           Key words: generative models, classical multidimensional scaling, concentration inequalities


                                           1     Introduction
                                           Generative models in artificial intelligence have found ubiquitous use in natural language processing
                                           (Devlin et al., 2019; Brown et al., 2020; Sanh et al., 2021), code generation (Zhang et al., 2023) and
                                           text-to-image generation (Crowson et al., 2022). Large langugae models in particular have the po-
                                           tential to revolutionize human-computer interaction (Bubeck et al., 2023). With the increase in use
                                           of generative models in different spheres of life, there has been a surge in demand for theoretically
                                           sound tools which can perform statistical analysis and inference tasks on a collection of black-box
                                           generative models. Moniri et al. (2024) proposes a novel method for evaluating the performances of
                                           a class of interacting language models. For the purpose of providing performance guarantees and
                                           unsupervised learning to investigate differences in model behaviour, various works (Faggioli et al.,
                                           2023; Duderstadt et al., 2023) explore and demonstrate the potential of response-based vector em-
                                           beddings of generative models for subsequent inference tasks. In particular, Helm et al. (2024b)
                                           discusses a novel technique for finding a vector representation for every generative model in a given
                                           collection of generative models, based on their responses to a set of queries. Acharyya et al. (2024)
                                           investigates the sufficient conditions under which the population-level vector representations for a
                                           class of generative models can be estimated consistently from their responses to a set of user-given
                                           queries, and Helm et al. (2024a) investigates the consistency of the sample vector representations
                                           for subsequent inference tasks.

                                           In this paper, we establish high probability concentration bounds for the vector representations for
                                           a collection of generative models based on their sample responses to a set of queries. The technique
                                           used in this paper for obtaining the vector representations is a variant of Data Kernel Perspective
                                           Space embedding, a technique for obtaining response-based vector embeddings of generative models,
                                           proposed in Helm et al. (2024a). Our study is based on a realistic scenario where the number of
                                           generative models, the number of queries and the number of samples or replicates can grow together.
                                           Under appropriate regularity conditions, these concentration bounds tell us that in order to estimate
                                           the population-level vector representations with a certain accuracy, how many sample responses are
                                           needed.

                                           We arrange the manuscript in the following manner. In Section 1.1, we introduce our notations.
                                           In Section 2, we describe the background and the motivation behind this work. We give a detailed
                                           description of the Data Kernel Perspective Space embedding method in Section 3, and subsequently
                                           introduce our theoretical results in Section 4. In Section 5, we present our numerical experiments,
                                           including the simulations in Section 5.1 and the real data analysis in Section 5.2. We conclude with
                                           a discussion on work in Section 6. We provide the proofs of our theoretical results in Section 7.

                                           1.1    Notations
                                           In this paper, every vector will be represented by a bold lower case letter such as v. Any vector
                                           by default is a column vector. Matrices will be denoted by bold upper case letters such as A. For


                                                                                                 1
```

## Page 2

```text
a matrix A, the (i, j)-th entry will be given by Ai,j , the i-th row (written as a column vector)
will be given by Ai· and the j-th column will be given by A·j . For any matrix A ∈ Rm×n with
rank(A) = r, the singular values in descending order will be given by σ1 (A) ≥ · · · ≥ σr (A), the
corresponding left singular vectors will be given by u1 (A), . . . , ur (A) and the corresponding right
singular vectors will be given by v1 (A), . . . vr (A). The n × n centering matrix will be denoted by
Hn = In − n1 (1n 1Tn ) where In is the n × n identity matrix and 1n is the n-length vector of all ones.
For a matrix A ∈ Rm×n , A[p:q,r:s] (where 1 ≤ p < q ≤ m, 1 ≤ r < s ≤ n) denotes the matrix
obtained by retaining the {p, (p + 1), . . . q}-th rows and {r, (r + 1), . . . s}-th rows of A, and A[p:q,.]
denotes the matrix obtained by retaining the {p, (p + 1), . . . q}-th rows and all the columns of A,
and A[.,r:s] denotes the matrix obtained by retaining the {r, (r + 1), . . . s}-th columns and all the
rows of A. For two matrices A, B ∈ Rm×n , the Hadamard product of A and B is given by
                        
      A ◦ B = Aij Bij                .
                           i∈[m],j∈[n]

Moreover, for any matrix A ∈ Rm×n , and for any exponent s ∈ R,
                 
      ◦s        s
     A = Aij               .
                     i∈[m],j∈[n]

For any matrix A, the spectral norm is denoted by ∥A∥ and the Frobenius norm is denoted by ∥A∥F .

For two sequences {an }∞            ∞
                       n=1 and {bn }n=1 , we use the following notations:

                                                   an
      an = o(bn ) ⇐⇒ bn = ω(an )          if lim        = 0,
                                            n→∞ bn
                                                                                          an
      an = O(bn ) ⇐⇒ bn = Ω(an )          if ∃ C > 0, n0 ∈ N such that for all n ≥ n0 ,      ≤ C.
                                                                                          bn

For a sequence of events {En }∞                 c
                              n=1 satisfying P[En ] = o(1), we say En occurs with high probability
for sufficiently large n.

Next, we discuss what is the background of this paper, and what motivated us to conduct this
investigation.



2     Background and Motivation
A generative model is a random map from an input space or query space (denoted by Q) to an out-
put space or response space (denoted by X ). For every query q ∈ Q, we denote the response by f (q).

It is of interest to develop methodologies for carrying out statistical inference tasks on a set of
generative models. However, generative models are typically black-boxes, that is, for a generative
model f : Q → X , we typically do not have access to the functional form of f . Hence, we analyse
the responses of the generative models to user-given queries to carry out inference on the generative
models. We quantify the response of a generative model to a query as a vector, using an embedding
function g : X → Rp , such that the vectorized response g(f (q)) ∈ Rp is a random vector whose
distribution depends on the query q and the generative model f . In reality, we do not know the dis-
tribution of g(f (q)), hence we obtain iid replicates g(f (q)1 ), . . . , g(f (q)r ) from which we empirically
estimate the response distribution and use it for subsequent inference.

In order to conduct statistical inference on a set of black-box generative models, several works
in the literature including Helm et al. (2024b) suggests embedding the given set of generative mod-
els into a finite-dimensional Euclidean space. In particular, Helm et al. (2024b) suggests performing
multidimensional scaling upon the pairwise dissimilarities between the distributions of the sample
responses of the generative models to some user-given queries, to obtain a vector representation of
every generative model in the given set of generative models. This method is termed Data Kernel
Perspective Space embedding.

Helm et al. (2024a) and Acharyya et al. (2024) investigate the asymptotic properties of the sample
vector embeddings, and establish consistency results under appropriate conditions. However, there
is a sharp increase in cost with the increase in sample size of responses from the generative models,
making the asymptotic regime unrealistic. Hence, it is of interest to obtain high probability con-
centration bounds for the sample vector embeddings, which provides guarantees for finite-sample
scenarios. To be precise, it can tell us that in order to reach a desired level of accuracy with a target
level of confidence, what the minimum size of the sample of responses should be.

In the next section, we describe the Data Kernel Perspective Space embedding method.



                                                        2
```

## Page 3

```text
3       Description of the Data Kernel Perspective Space embed-
        ding method
Our setting involves a set of generative models {f1 , . . . , fn }, each of which is a random map from
a common query space Q to a common response space X . Each generative model responds to a
set of user-given queries, {q1 , . . . , qm } ⊂ Q. There is an embedding function g which maps every
response to a vector in Rp . The distribution of the (vectorized) response of fi to qj is Fij , that is,
g(fi (qj )) ∼ Fij for all i, j.

In reality, Fij is supported on a bounded subset of Rp , which implies that Fij has finite mo-
ments of every order. At the population-level, the generative model fi is represented by the matrix
                                                      T
µi = E[g(fi (q1 ))] E[g(fi (q2 ))] . . . E[g(fi (qm ))]   ∈ Rm×p for all i, in the context of the given
queries. The population-level pairwise dissimilarities between the generative models are given by
                         1
∆ii′ = √1m ∥µi − µi′ ∥F2 . Classical Multidimensional Scaling of the pairwise dissimilarities ∆ii′ into
Rd yields vectors ψ 1 , . . . , ψ n ∈ Rd .

In reality, we cannot compute the vectors ψ i because the response distributions Fij are unknown.
Hence, we obtain iid replicates of responses for each model to every query, that is, for every i, j, we
obtain
        g(fi (qj )1 ), . . . , g(fi (qj )r ) ∼iid Fij ,
where fi (qj )k denotes the k-th replicate of the response of fi to qj . We estimate µi with its sam-
                         Pr                  Pr                          Pr                T
ple counterpart X̄i = 1r k=1 g(fi (q1 )k ) 1r k=1 g(fi (q2 )k ) . . . | 1r k=1 g(fi (qm )k ) . We perform
Classical Multidimensional Scaling upon the sample dissimilarity matrix D given by
                                n
                1              1
      D=      √     X̄i − X̄i F
                             ′
                               2
                                          ,
                m                 i,i′ =1

to obtain the sample vector embeddings {ψ̂ 1 , . . . , ψ̂ n }.
We describe the algorithm for the abovementioned procedure, referred to as Data Kernel Perspective
Space embedding, in Algorithm 1a below.

Algorithm 1a DKPSembed({fi }ni=1 ; {qj }m j=1 ; r; g; d)
.
  1: Generate r independent and identically distributed replicates of responses from every model fi
     to every query qj , that is, obtain

              g(fi (qj )1 ), . . . , g(fi (qj )r ) ∼iid Fij for all i, j.
                                                                                                                             T
                                                  1
                                                      Pr                 1
                                                                             Pr                         1
                                                                                                            Pr
 2: For every i, compute X̄i =                    r    k=1 g(fi (q1 )k ) r    k=1 g(fi (q2 )k )   ...   r    k=1 g(fi (qm )k )   ∈
        m×p
    R         .                                                            n
                                                                          1
 3: Compute the matrix of dissimilarities, D =                        √1
                                                              X̄i − X̄i′ F2           .
                                                                       m
                                                                       h     i,i′ =1         i
 4: Obtain B̂         = − 21 Hn D◦2 HTn , compute Û(d) =               u1 (B̂) . . . ud (B̂) and Ŝ(d)                         =
                                                                                 21
    diag(λ1 (B̂), . . . , λd (B̂)), and subsequently calculate ψ̂ = Û(d) Ŝ(d)         ∈ Rn×d .
 5: return {ψ̂ 1 , . . . ψ̂ n } where ψ̂ i is the i-th row of ψ̂.


Remark 1. We shall henceforth refer to the vector ψ i as the true perspectives of the generative
model fi , and ψ̂ i as the estimated perspective of fi for all i (in the context of the set of queries
{qj }m
     j=1 ).

   For sake of convenience, we shall henceforth use the notations B = − 12 Hn ∆◦2 HTn , and B̂ =
− 12 HTn D◦2 HTn .
                Moreover, λ1 , λ2 , . . . , λn denote the eigenvalues of B arranged in decreasing order
of magnitude (that is, |λ1 | ≥ |λ2 | ≥ · · · ≥ |λn |), and λ̂1 , λ̂2 , . . . , λ̂n denote the eigenvalues of B̂
arranged in decreasing order of magnitude (that is, |λ̂1 | ≥ |λ̂2 | ≥ · · · ≥ |λ̂n |).

In the following sections, we establish a high probability concentration bound on the estimation
error of the perspectives, and subsequently demonstrate its applicability in a subsequent inference
task.



4       Theoretical results
We present our theoretical results in this section. Our key concentration inequality result holds for
any finite collection of generative models, but since we want the estimation error to be smaller with


                                                                    3
```

## Page 4

```text
high probability as the number of generative models (n) grows, we show that our estimation error
approaches zero in the asymptotic regime. Since we draw our inferences on the generative models
from the sample responses, we expect that the number of sample responses to every query (r) must
also grow sufficiently fast as the number of generative models increases, to ensure that the estimation
error approaches zero with high probability.

Recall that the estimated perspectives ψ̂ i are obtained by Classical Multidimensional Scaling of
the (doubly centered) sample dissimilarity matrix B̂ (while the true perspectives ψ i are Classical
Multidimensional Scaling outputs of B). Thus, in order to establish a concentration bound on the
error of estimation of ψ by ψ̂, it would be helpful to obtain a concentration bound on B̂ − B . Our
following result establishes an entrywise bound, which is subsequently used to establish a spectral
norm bound.
Theorem 1. In our setting, suppose Σij ∈ Rp×p is the covariance matrix associated with the
distribution Fij , and let γij = trace(Σij ). Then, for any ϵ > 0,
                                                  Pn Pm
        h
                                         ′
                                           i    16 i=1 j=1 γij
      P |B̂ii′ − Bii′ | < ϵ, for all i, i ≥ 1 −                  .
                                                     rmϵ2
    Since γij is the trace of the dispersion matrix of the distribution of responses of fi to qj , it
denotes a measure for variability of the response distribution of fi to qj . That is, a large value of
γij is associated with a large variation amongst the responses of fi to qj . The above result says that
when γij are sufficiently small and m, n and r maintain a suitable relationship amongst themselves,
every entry of B̂ is close to its population counterpart B with high probability. Also, note that if
all γij are uniformly bounded by a constant, then the number of queries, m, does not matter. If all
the entries of B̂ are close to those of B, then B̂ is close to B is Frobenius norm, and hence also in
spectral norm. Our next result establishes a high probability bound on B̂ − B , under appropriate
conditions.
Corollary 1. In our setting, assume that supi,j γij = O(1), and r = ω(n3 ). Then, for any δ ∈ (0, 12 ),
for sufficiently large n and r, with high probability,
                            12 −δ
                      n3
                  
       B̂ − B <                      .
                      r

    Corollary 1 establishes a bound on the spectral norm B̂ − B , under the condition that the
variability γij of the response distributions Fij are uniformly bounded by a constant, and the sample
size r grows faster than n3 . Note that if the variability terms γij grew with n, then r would have
needed an even faster rate of increase than n3 .

The spectral norm bound established in Corollary 1 can be used to establish concentration bound
on the estimation error ψ̂W∗ − ψ , using Weyl’s Inequality, which puts a bound on the eigenvalue
perturbations, and Davis Kahan Theorem, which puts a bound on the eigenvector perturbations.
We make extensive use of the results in Agterberg et al. (2022), where ψ̂W∗ − ψ is decomposed
into a sum of matrices. We establish a bound on each summand matrix, and thus establish our key
concentration result.

Prior to stating our key concentration result, we discuss the assumptions under which our result
holds.
Assumption 1. For all n sufficiently large, rank(B) = d where d is a constant not changing with
n.
   Note that Assumption 1 states that the true perspectives ψ i of the generative models reside in
a d-dimensional Euclidean space. Assumption 1 is based on our observation that in simulation and
synthetic data analysis, we find that our (doubly centered) dissimilarity matrices have an elbow
at approximately the same value. It justifies our choosing the same embedding dimension as the
number of generative models under consideration grows.

While Assumption 1 is not a strict necessity for deriving concentration bounds on the sample em-
beddings, it does facilitate convenient analysis and interpretation. Consider, for instance, a regime
where the B grows with n, thus violating Assumption 1. In such case, the perspective of a specific
generative model has a growing number of components as more generative models are brought un-
der consideration. This makes comparison across different sub-regimes difficult. For instance, if one
wants to study the change in perspective of a specific generative model as n grows, it is inconvenient
to deal with vectors of growing dimensions. Nonetheless, we recognize that Assumption 1 needs to
be relaxed for taking into account more generalized scenarios, and we leave that to future work.
Below, we state our next assumption.



                                                  4
```

## Page 5

```text
Assumption 2. There exist constants C1 , C2 > 0 such that lim inf n λd > C1 and lim supn λ1 < C2 .
    Recall that the λ1 ≥ λ2 ≥ · · · ≥ λd are the d non-zero eigenvalues of the population-level (dou-
bly centered) dissimilarity matrix B. Thus, it becomes apparent that Assumption 2 is a stability
condition on the eigenvalues of the (doubly centered) population dissimilarity matrix. On one hand,
it ensures that the matrix B is always well-conditioned no matter how large n is, that is, it ensures
that even when we consider a large number of generative models, the (doubly centered) matrix of
the population dissimilarities is stable to minute perturbations. On the other hand, it also ensures
that all the components of the true perspectives ψ i are comparable (in magnitude) to one another.

Consider, for instance, a regime where Assumption 2 is violated. If lim inf n |λd | = 0, then in-
finitely often the d-th component in the perspectives do not matter, which makes the embedding in
d-dimension less parsimonious. In such case, embedding in (d − 1)-dimension is more reasonable. If
lim supn |λ1 | = ∞, then infinitely often the first component of the perspectives blow up, making the
embedding in d-dimension futile. Our next result states the sufficient condition for Assumptions 1
and 2 to hold.
Proposition 1. Assumption 1 and Assumption 2 hold when every generative model fi is associated
with a vector ϕi on a d-dimensional compact Riemannian manifold M in a high-dimensional ambient
space Rq , such that the pairwise geodesic distances dM (ϕi , ϕi′ ) equates to the pairwise population-
level dissimilarities between the mean (vector-embedded) responses of fi and fi′ , given by ∆ii′ .
    Next, we establish our main result stating a high probability concentration bound on the error
of estimating ψ with ψ̂ (upto an orthogonal transformation).
Theorem 2. In our setting, suppose r = ω(n3 ), and supi,j γij = O(1). Then, under Assumption 1
and Assumption 2, there exists an orthogonal matrix W∗ ∈ O(d) such that for every δ ∈ (0, 12 ), for
sufficiently large n and r,
                                 3  12 −δ !
                                  n
        ψ̂W∗ − ψ        ≤ Poly3                                                                 (1)
                    2,∞           r
                                               P3            i
with high probability, where Poly3 (x) =          i=0 Ci x       is a cubic polynomial in x, with coefficients

     C0 = 0,
                 (                √       )
           1            √      2d(1 + 2d)
     C1 = √       (1 + 2) +         √       ,
            λd                  1+ 2
                 1 !       (           √ )
               λ12      1       2d(3 + 2)
     C2 = 4d         + 3 1+           √       ,
               λ2d     λd2        1+ 2
              (      √                     !)
           1        8 2 + 16(1 + d)    √
     C3 = 5 d               √       +4 2        .
          λd2           1+ 2

    Thus, in a setting where the response distributions have uniformly bounded variability (that is,
supi,j γij = O(1)), the abovementioned Theorem 2 yields a high probability concentration bound
for the sample vector embeddings of a finite number of generative models. Note that Assumptions
1 and 2 ensures that the coefficients of the polynomial upper bound in Equation (2) are bounded
above. Hence, by making the sample size r grow faster than n3 , we can achieve any desired level of
accuracy. We state this result formally in the following corollary.
Corollary 2. In our setting, suppose r = ω(n3 ) and γij = O(1) for all i, j. Then, under Assumption
                                                                       (n)
1 and Assumption 2, there exists a sequence of orthogonal matrices W∗ ∈ O(d) such that for some
        1
δ ∈ (0, 2 ),
                                            21 −δ !
                                      n3
                                  
          (n)
       ψ̂W∗ − ψ            = OP                        .
                     2,∞              r

    The above corollary summarizes the information on the rate of convergence of the uniform
estimation error, given by ψ̂W∗ − ψ     . After presenting our theoretical results in the current
                                               2,∞
section, we back them up with our results from numerical experiments in the next section.


5    Numerical Experiments
We present our numerical results in this section. At first, we present our simulations in Section 5.1.
In our simulations, we simulate the responses from a real large language model with high dimensional
random vectors, and demonstrate that our concentration bounds exhibit high empirical coverage.
Then, in Section 5.2, we generate responses from an actual large language model to demonstrate
the high empirical coverage for our theoretically derived concentration bounds.


                                                           5
```

## Page 6

```text
  n    m     average minW∈O(d) ∥ψ̂W − ψ∥               upper bound        Empirical Coverage
 10     3                  0.000426                      0.704184                  100%
 12     3                  0.000308                      0.542679                  100%
 15     3                  0.000201                      0.395877                  100%
 18     3                  0.000146                      0.318522                  100%
 20     3                  0.000021                      0.279479                  100%

Table 1: Analysis of vector embeddings obtained by simulating responses from LLMs with high dimensional vectors, based
on 100 Monte Carlo samples for each value of n. The number of queries remain constant at 3. The third column represents
the average estimation error over all 100 Monte Carlo samples, which is found to be sufficiently smaller than the suggested
upper bound.



5.1     Simulations
Here, we simulate a large language model which outputs binary responses, with a Bernoulli ran-
dom number generator. We vary n in {10, 12, 15, 18, 20}, keep m = 2 and r = n5.5 . For every
n ∈ {10, 12, 15, 18, 20}, we do the following. First, we construct n arrays of m uniform random
numbers in (0, 1), where the i-th array is meant to be the probabilities of responding “Yes” to
the m queries. Thus, in our case, µi ∈ Rm is just a vector, and we compute the eigenvalues of
B = − 12 Hn ∆◦2 Hn , and use the scree plot to determine an appropriate value of d, and thus obtain
ψ = CMDS(∆, d). After that, we compute the value of the expression in the Right Hand Side
of Equation 2. Then, we compute the values of arg minW∈O(d) ψ̂W − ψ                              on 100 Monte Carlo
samples, and compute on what proportion of them Equation 2 is satisfied.

We find that our bound is satisfied on 100% of the Monte Carlo samples, for every n. The bound
is found to be of the order of 10−1 , while on an average the quantity arg minW∈O(d) ψ̂W∗ − ψ is
of the order 10−4 , for our choice of hyperparameters. The tabulated values of the estimation error
and its high probability upper bound are given in Table 1.




5.2     Real Data Analysis
We use Google-gemma-2-2b-it to run the experiments. We set m = 2 where the queries are
q1 = “How do outliers impact statistical results?” and
q2 = “What role does education play in social mobility?”.
We use nomic-ai/nomic-embed-text-v2-moe to transform the responses to vectors in R768 . We
vary n, the number of LLMs, in the range {10, 12, 14, 16} and use r = n5 to be the number of
replicates of responses sampled for the practitioner to compute ψ̂.

For every n, we perform the following procedure. We first sample R = n3.75 replicates of responses
(denoted by xij1 , . . . , xijR ) for every LLM fi to every query qj , which we use to compute the ma-
trices µi ∈ R2×768 . Subsequently, we compute the population dissimilarity matrix ∆ and calculate
ψ ∗ ∈ CMDS(∆, d) where d is the rank of the doubly centered dissimilarity matrix B = − 21 Hn ∆Hn .
It is found that d = 3 for every n in our case. Then, on each of 100 Monte Carlo samples, we
                                                                 (b)       (b)
bootstrap r = n5 replicates of the responses (denoted by {xij1 , . . . , xijr } for the b-th Monte Carlo
sample) from the original pool of R generated responses ({xij1 , . . . , xijR }), for every LLM fi to
every query qj . We use the bootstrapped sample responses to compute the matrices X̄i ∈ R2×768 ,
compute the sample dissimilarity matrix D and subsequently compute the sample embedding matrix
ψ̂ ∈ Rn×d . For each n, we compute the quantity arg minW∈O(3) ψ̂W − ψ ∗ on each of the 100
Monte Carlo samples, and compute what proportion of them exceed the upper bound Un , which is
computed from the Right Hand Side of Equation 2.




                                                            6
```

## Page 7

```text
    n     m     average minW∈O(d) ∥ψ̂W − ψ∥              upper bound        Empirical Coverage
 10        2                 0.0023                            10.75                 100%
 12        2                 0.0013                             4.37                 100%
 14        2                 0.0008                             2.31                 100%
 16        2                 0.0006                             1.78                 100%

Table 2: Analysis of real data from large language model Google-gemma-2-2b-it, based on 100 Monte Carlo samples for each
value of n. The number of queries remain the same (2). The third column represents the average estimation error over 100
Monte Carlo samples, which can be seen to be sufficiently smaller than the upper bound on the fourth column. For every
value of n, on all the Monte Carlo samples the upper bound is found to be satisfied.




Figure 1: Violin plot (left panel) and histogram (right panel) of the values of estimation error y = minW∈O(d) ψ̂W − ψ
over 100 Monte Carlo samples for each of n = 4, 6, 8, 10, 12. For each value of n, every generative model provides r = n5
i.i.d. responses to every query on each of 100 Monte Carlo samples. Both the figures show that as n increases, the estimation
error gets more concentrated toward zero.


        We tabulate our findings in Table 2.




6         Discussion
To facilitate statistical analysis and inference on a given set of black-box generative models, vari-
ous works in literature propose embedding every generative model in the given class into a finite-
dimensional Euclidean space, based on their responses to user-given queries. The vector embeddings
thus obtained can be used for further downstream tasks such as providing performance guarantees
or identification of models with sensitive information. Helm et al. (2024b) proposes one such em-
bedding method, known as the DKPS (Data Kernel Perspective Space) Embedding, which obtains
a response-based vector embedding for every member of a given set of generative models, by using
i.i.d responses from generative models to every query.

In this paper, we obtain high probability concentration bounds for the DKPS vector embeddings.
We show that if the number of i.i.d responses from a generative model to a query grows sufficiently
faster than the number of generative models in the given set, then we can bound the error for esti-
mation of the population-level vector
                                 3  embeddings with a quantity that is a polynomial function of
a positive power of the quantity nr .

This gives us the ability to decide what the sample size r should be, for a particular inference
problem, for reaching a desired level of accuracy. First, note that a spectral norm bound is also
a uniform bound, because ψ̂W∗ − ψ           ≤ ψ̂W∗ − ψ . Hence, using our key result Theorem
                                                  2,∞
2, we can estimate how large r should be in order to ensure that all the estimated perspectives
ψ̂ i are within a desired proximity of their population counterparts ψ i (up to a rotation), with high
probability. This essentially lets us decide the sample size r in order to obtain a desired level of accu-
racy on inference tasks (which are invariant to orthogonal transformations) involving the estimated
perspectives ψ̂ i . Take, for instance, the problem of testing, whether two specific generative models
have the same perspective, in a collection of n generative models. That is, without loss of generality,
we want to test H0 : ψ 1 = ψ 2 . Clearly, we shall use the test statistic Tn,m,r = ψ̂ 1 − ψ̂ 2 . Then,
using Theorem 2, we can ensure ψ̂W∗ − ψ                        ≤ κ for any desired κ > 0, with high probability,
                                                         2,∞
by choosing a sufficiently large r. This means, by choosing a sufficiently large r, we can conclude



                                                             7
```

## Page 8

```text
that ψ 1 ̸= ψ 2 with high probability, when we observe ψ̂ 1 − ψ̂ 2 > 2κ.

Our results are derived under the condition that the distributions of the responses of the gener-
ative models have uniformly bounded variability (that is, supi,j γij = O(1)). This condition is based
on the fact that in reality, the tokens (which are the building blocks of a response from a generative
model) are sampled from a finite pool of tokens. However, we can impose more stringent condition
on sampling of tokens (in reality, this is achieved by lowering the temperature of a generative model),
which will ensure that the average
                              Pm      variability of every generative model decreases as the number of
queries increase, that is, m1
                                j=1 γ ij = O(m−η ) for all i (where η is some positive number). Under
appropriate conditions, that will imply that the concentration bound on B̂ − B depends on m,
apart from n and r. In practice, this means one can manipulate the concentration bounds not just
by changing the number of replicates (r), but also by changing the number of queries (m).

We discuss the scopes for future extension of our work in this paragraph. Primarily, as shown
in Table 1 and Table 2, the bounds for the estimation error minW∈O(d) ψ̂W − ψ are not sharp,
and hence there is a room for improvement. Secondly, our work discusses bounds under the con-
dition r = ω(n3 ). In reality, for reasonable values of n, it is costly to obtain r = ω(n3 ) replicates
of responses, and hence investigation of concentration bounds for a slower rate of increase in r will
be of importance. Finally, we discuss the bounds on error measured in terms of Frobenius norm,
whereas a bound on two-to-infinity norm (that is, a bound on minW∈O(d) ψ̂W − ψ                 ) would
                                                                                           2,∞
have captured a uniform bound on the estimation error. Hence, investigation on uniform bounds on
estimation error is a possible future extension of our work.

We have not come across work of similar nature in the literature, pertaining to obtaining concen-
tration bounds on response-based generative model embeddings. Since we consider response-based
embeddings of generative models, it enables us to deal with generative models in a realistic black-
box setting. The concentration bounds offer us finite-sample guarantees, facilitating theoretical
foundation for study in the non-asymptotic regime.




                                                  8
```

## Page 9

```text
References
Aranyak Acharyya, Michael W Trosset, Carey E Priebe, and Hayden S Helm. Consistent estima-
  tion of generative model representations in the data kernel perspective space. arXiv preprint
  arXiv:2409.17308, 2024.
Joshua Agterberg, Zachary Lubberts, and Jesús Arroyo. Joint spectral clustering in multilayer
  degree-corrected stochastic blockmodels. arXiv preprint arXiv:2212.05053, 2022.

Tom Brown, Benjamin Mann, Nick Ryder, Melanie Subbiah, Jared D Kaplan, Prafulla Dhariwal,
  Arvind Neelakantan, Pranav Shyam, Girish Sastry, Amanda Askell, et al. Language models are
  few-shot learners. Advances in neural information processing systems, 33:1877–1901, 2020.
Sébastien Bubeck, Varun Chadrasekaran, Ronen Eldan, Johannes Gehrke, Eric Horvitz, Ece Kamar,
   Peter Lee, Yin Tat Lee, Yuanzhi Li, Scott Lundberg, et al. Sparks of artificial general intelligence:
   Early experiments with gpt-4, 2023.
Yuxin Chen, Yuejie Chi, Jianqing Fan, Cong Ma, et al. Spectral methods for data science: A
  statistical perspective. Foundations and Trends® in Machine Learning, 14(5):566–806, 2021.
Katherine Crowson, Stella Biderman, Daniel Kornis, Dashiell Stander, Eric Hallahan, Louis Cas-
 tricato, and Edward Raff. Vqgan-clip: Open domain image generation and editing with natural
 language guidance. In European conference on computer vision, pages 88–105. Springer, 2022.
Jacob Devlin, Ming-Wei Chang, Kenton Lee, and Kristina Toutanova. Bert: Pre-training of deep
  bidirectional transformers for language understanding. In Proceedings of the 2019 conference of
  the North American chapter of the association for computational linguistics: human language
  technologies, volume 1 (long and short papers), pages 4171–4186, 2019.
Brandon Duderstadt, Hayden S Helm, and Carey E Priebe. Comparing foundation models using
  data kernels. arXiv preprint arXiv:2305.05126, 2023.
Guglielmo Faggioli, Laura Dietz, Charles LA Clarke, Gianluca Demartini, Matthias Hagen, Claudia
 Hauff, Noriko Kando, Evangelos Kanoulas, Martin Potthast, Benno Stein, et al. Perspectives on
 large language models for relevance judgment. In Proceedings of the 2023 ACM SIGIR Interna-
 tional Conference on Theory of Information Retrieval, pages 39–50, 2023.
Hayden Helm, Aranyak Acharyya, Brandon Duderstadt, Youngser Park, and Carey E Priebe.
  Embedding-based statistical inference on generative models. arXiv preprint arXiv:2410.01106,
  2024a.

Hayden Helm, Brandon Duderstadt, Youngser Park, and Carey E Priebe. Tracking the perspectives
  of interacting language models. arXiv preprint arXiv:2406.11938, 2024b.
Behrad Moniri, Hamed Hassani, and Edgar Dobriban. Evaluating the performance of large language
  models via debates. arXiv preprint arXiv:2406.11044, 2024.

Victor Sanh, Albert Webson, Colin Raffel, Stephen H Bach, Lintang Sutawika, Zaid Alyafeai, An-
  toine Chaffin, Arnaud Stiegler, Teven Le Scao, Arun Raja, et al. Multitask prompted training
  enables zero-shot task generalization. arXiv preprint arXiv:2110.08207, 2021.
Yi Yu, Tengyao Wang, and Richard J Samworth. A useful variant of the davis–kahan theorem for
  statisticians. Biometrika, 102(2):315–323, 2015.

Shun Zhang, Zhenfang Chen, Yikang Shen, Mingyu Ding, Joshua B Tenenbaum, and Chuang Gan.
  Planning with large language models for code generation. arXiv preprint arXiv:2303.05510, 2023.




                                                   9
```

## Page 10

```text
7     Appendix
7.1    Proofs of theorems and corollaries
 Theorem 1. In our setting, suppose Σij ∈ Rp×p is the covariance matrix associated with the
distribution Fij , and let γij = trace(Σij ). Then, for any ϵ > 0,
                                                  Pn Pm
        h
                                         ′
                                           i    16 i=1 j=1 γij
      P |B̂ii′ − Bii′ | < ϵ, for all i, i ≥ 1 −                  .
                                                     rmϵ2
                                   2                                      1
Proof. P   Define Eii′ = D2ii′ −P∆ ii′ and note that |B̂   ii′ − Bii′ | = 2 Eii′ − Ēi· − Ē·i′ + Ē·· , where
       1    n                 1  n                     1
                                                          P  n
Ēi· = n i′ =1 Eii′ , Ē·i′ = n i=1 Eii′ and Ē·· = n2 i,i′ =1 Eii′ . Hence,
         h                              i
      P B̂ii′ − Bii′ < ϵ, for all i, i′ = P Eii′ − Ēi· − Ē·i′ + Ē·· < 2ϵ, for all i, i′
                                                                                            
                                             h           ϵ           ϵ            ϵ         ϵ                i
                                          ≥ P |Eii′ | < , |Ēi· | < , |Ē·i′ | < , |Ē·· | < , for all i, i′
                                                         2           2 i          2         2
                                             h           ϵ              ′
                                          = P |Eii′ | < , for all i, i
                                                        2                      
                                               1                   ϵ
                                          ≥P        X̄i − µi < , for all i
                                               m                   4
                                                   Pn Pm
                                               16 i=1 j=1 γij
                                          ≥1−                         .
                                                        rmϵ2



Corollary 1. In our setting, assume that for all i, j, γij = O(1), and r = ω(n3 ). Then for
any δ ∈ (0, 12 ), with high probability,
                               12 −δ
                        n3
                    
       B̂ − B <                         .
                        r
                         n                         o  n            o  n            o
Proof. We know that B̂ii′ − Bii′ < ϵ, for all i, i′ ⊆   B̂ − B < nϵ ⊆   B̂ − B < nϵ .
                                                              F
Thus, replacing ϵ with nϵ in Theorem 1,
                                   Pn Pm
       h             i        16n2 i=1 j=1 γij
     P B̂ − B < ϵ ≥ 1 −                        .
                                     rmϵ2
                                                                          1
Under the condition γij = 1 for all i, j, selecting ϵ =                       1 −δ   for some δ > 0, we can see that
                                                                     ( nr3 ) 2
                                                          !
                                1                     1
      P  B̂ − B <              1  ≥ 1 − O                     .
                               r 2 −δ                r 2δ
                                                       
                              n3                     n3

Since r = ω(n3 ),
                             1
       B̂ − B <               12 −δ
                        r
                        n3

with high probability.



Theorem 2. In our setting, suppose r = ω(n3 ), and supi,j γij = O(1). Then, under Assumption 1
and Assumption 2, there exists an orthogonal matrix W∗ ∈ O(d) such that for every δ ∈ (0, 12 ), for
sufficiently large n and r,
                                 3  12 −δ !
                                  n
        ψ̂W∗ − ψ        ≤ Poly3                                                                 (2)
                    2,∞           r
                                                P3          i
with high probability, where Poly3 (x) =         i=0 Ci x       is a cubic polynomial in x, with coefficients
      C0 = 0,
                    (                     ) √
            1                  √
                               2d(1 + 2d)
      C1 = √      (1 + 2) +         √       ,
             λd                 1+ 2
                 1 !       (           √ )
               λ12      1       2d(3 + 2)
      C2 = 4d        + 3 1+           √       ,
               λ2d     λd2        1+ 2
              (      √                     !)
            1       8 2 + 16(1 + d)    √
      C3 = 5 d              √       +4 2        .
           λ2           1+ 2
              d


                                                          10
```

## Page 11

```text
Proof. From Theorem 2, using Triangle Inequality,
                                                     6
                    1         X
       ψ̂W∗T − ψ ≤ √ B̂ − B +     ∥Rk ∥ .
                     λ        k=1

We know that, for every δ ∈ (0, 21 ), for suffciently large n and r, with high probability,
                                                           √  3  1 −δ
                                                             2 n 2
                                                             1                ∥R1 ∥ ≤
                                                                           [from Proposition-A.1]
                                                           λ2       r
                       √       (           3  12 −δ         1−2δ )
                         2  d               n            8d n3
              ∥R2 ∥ ≤    √ √     (1 + 2d)             +                    [from Proposition-A.2]
                      1+ 2 λ                r             λ      r
                                                                 3 1−2δ
                                                    4d       1     n
                                          ∥R3 ∥ ≤ 2 ∥B∥      2
                                                                           [from Proposition-A.3]
                                                    λ              r
                                                                 1−2δ
                                                            1 n3
                                                ∥R4 ∥ ≤ 3                  [from Proposition-A.4]
                                                           λ2      r
                  (         3 1−2δ      √                3( 12 −δ) )
            1  2d      √    n           4 2 + 8(1 + d) n3
 ∥R5 ∥ ≤     √ 3 (3 + 2)             +                                     [from Proposition-A.5]
         1 + 2 λ2            r                 λ              r
                                                      √  3( 1 −δ)
                                                    4 2d n3           2

                                           ∥R6 ∥ ≤      5                 [from Proposition-A.6].
                                                      λ2        r

Using Proposition 1-6 and Corollary 1, for sufficiently large n and r, with high probability,
                         (           3  12 −δ √                  3  12 −δ )            3 1−2δ
          T           1        √      n              2d(1 +  2d)   n              4d    1  n
      ψ̂W∗ − ψ ≤ √         (1 + 2)              +         √                     + 2 ∥B∥ 2

                       λ               r              1+ 2          r             λ         r
                            (            √    )   3 1−2δ         (        √                   !)  3( 1 −δ)
                         1       2d(3 + 2)         n             1        8 2 + 16(1 + d)     √     n3   2

                      + 3 1+            √                   + 5 d                  √      +4 2                 .
                        λ2         1+ 2            r           λ2               1+ 2                r

Proposition A.1. In our setting, suppose r = ω(n3 ). Then, there exists a constant C1 > 0 such
that for sufficiently large n and r, with high probability,
             √  3  1 −δ
              2 n 2
      ∥R1 ∥ ≤ 1           .
             λ2  r

                                                                         1                           1
Proof. Recall that R1 = −UUT (B̂ − B)Û|Λ̂|− 2 Ip,q , which implies ∥R1 ∥ ≤ B̂ − B              |Λ̂|− 2 .
Using Corollary 1 and Lemma 3, for sufficiently large n and r, with high probability,
                             12 −δ                          √
                       n3
                   
                                                 − 12            2
       B̂ − B ≤                       ,       |Λ̂|       ≤       1   .
                       r                                     λ   2



Thus, for sufficiently large n and r, with high probability,
                √  3  1 −δ
                 2 n 2
      ∥R1 ∥ ≤    1           .
                λ2  r



Proposition A.2. In our setting, suppose r = ω(n3 ). Then, for sufficiently large n and r, with
high probability,
                  √      (           3  12 −δ      1−2δ )
                    2  d             n            8d n3
      ∥R2 ∥ ≤       √ √    (1 + 2d)             +             .
               1+ 2 λ                 r           λ  r

Proof. Recall that,
                             1            1                                             1   1
      R2 = U(UT Û|Λ̂| 2 − |Λ| 2 UT Û) =⇒ ∥R2 ∥ ≤ UT Û|Λ̂| 2 − |Λ| 2 ÛT U .

Using Lemma 4, we deduce that for sufficiently large n and r, with high probability,
              √       (           3  12 −δ        1−2δ )
                2   d              n            8d n3
     ∥R2 ∥ ≤    √ √     (1 + 2d)             +                  .
             1+ 2 λ                 r            λ    r



                                                                         11
```

## Page 12

```text
    Proposition A.3. In our setting, suppose r = ω(n3 ). For sufficiently large n and r, with high
probability,
                                           1−2δ
                                      n3
                                  
             4d     1
      ∥R3 ∥ ≤ 2 ∥B∥ 2                              .
             λ                        r

Proof. We know,
                             1
      ∥R3 ∥ = U|Λ| 2 (UT Û − W∗ ),

which gives us
                         1
      ∥R3 ∥ ≤ ∥B∥ 2 UT Û − W∗
                         1
            ≤ ∥B∥ 2 UT Û − W∗
                                                   F
                         1
            = ∥B∥        2
                                 I − cosΘ(U, Û)
                                                           F
                         1                         2
            ≤ ∥B∥        2
                                 sinΘ(U, Û)
                                                   F
             4d     1       2
            ≤ 2 ∥B∥ 2 B̂ − B ,
             λ
where the last inequality follows from Davis-Kahan Theorem (Yu et al., 2015).
                                                                              1
                                                                                 3 1−2δ
Thus, for sufficiently large n and r, with high probability, ∥R3 ∥ ≤ λ4d2 ∥B∥ 2 nr        .

Proposition A.4. In our setting, suppose r = ω(n3 ). Then, for sufficiently large n and r, with
high probability,
                                  1−2δ
                             n3
                         
                 1
      ∥R4 ∥ ≤        3                     .
                 λ2          r

Proof. We know,
                                                           1
      R4 = (B̂ − B)(ÛÛT U − U)|Λ|− 2 Ip,q .

Hence,
                                                 1
      ∥R4 ∥ ≤ B̂ − B                sinΘ(U, Û) √
                                                  λ
                 1                     2
            ≤        3   B̂ − B            ,
                 λ   2


using Davis-Kahan theorem from Yu et al. (2015). Using Corollary 2, we get that for sufficiently
large n and r, with high probability,
                                  1−2δ
                             n3
                         
                 1
      ∥R4 ∥ ≤        3                     .
                 λ2          r


Proposition A.5. In our setting, suppose r = ω(n3 ). Then for sufficiently large n and r, with high
probability,
                      (            3 1−2δ     √               3( 12 −δ) )
                1  2d         √     n          4 2 + 8(1 + d) n3
     ∥R5 ∥ ≤     √ 3 (3 + 2)                 +                                  .
             1 + 2 λ2                r                λ            r

Proof. We know,
                                                       1       1
      R5 = −(B̂ − B)Û(ÛT U|Λ|− 2 Ip,q − |Λ̂|− 2 Ip,q ÛT U)

which implies
                                                       1       1
      ∥R5 ∥ ≤ B̂ − B                ÛT U|Λ|− 2 Ip,q − |Λ̂|− 2 Ip,q ÛT U .

Using Lemma 5, for sufficiently large n and r, with high probability,
                         (           3 1−2δ      √               3( 12 −δ) )
                1   2d          √     n           4 2 + 8(1 + d) n3
     ∥R5 ∥ ≤     √ 3 (3 + 2)                   +                                 .
             1 + 2 λ2                  r                 λ           r




                                                                   12
```

## Page 13

```text
Proposition A.6. In our setting, suppose r = ω(n3 ). Then, for sufficiently large n and r, with
high probability,
                 √  3( 1 −δ)
                4 2d n3  2

      ∥R6 ∥ ≤     5            .
                 λ2  r
                                                             1
Proof. We know, R6 = (B̂−B)Û|Λ̂|− 2 Ip,q (W∗T − ÛT U). Using the proof of Lemma C.4 in Section
C.1 (Agterberg et al. (2022)),

        W∗ − UT Û ≤ ∥I − cosΘ∥
                            ≤ ∥I − cosΘ∥F
                                                         2
                            ≤ sinΘ(U, Û)
                                                         F
                             4d       2
                            ≤ 2 B̂ − B .
                             λ
We know, for sufficiently large n and r, with high probability,
                                12 −δ
                          n3
                      
        B̂ − B ≤                           ,
                          r
                                   √
                        1              2
                |Λ̂|− 2        ≤       1   .
                                   λ   2


Thus, for sufficiently large n and r, with high probability,
               √  3( 1 −δ)
              4 2d n3  2

      ∥R6 ∥ ≤   5            .
               λ2  r

7.2     Proofs of Lemmas
 Lemma 1. In our setting, suppose r = ω(n3 ). Then, for sufficiently large n and r, with high
probability,

                                                             (         12 −δ                     1−2δ )
                                                                  n3                          n3
                                                                                          
                  T                T                                               4
        |Λ̂|(Ip,q Û U − Û UIp,q ) ≤ 2d                                         +                           .
                                                                  r                λ          r

   Proof. Observe that

                                                                      2|Λ̂+ |ÛT+ U−
                                                                                   
                                                           0
          
      |Λ̂| Ip,q ÛT U − ÛT UIp,q =
                                                     −2|Λ̂− |ÛT− U+         0
                                                      p×q
                                                                     −|Λ̂− |ÛT− U+        0q×q
                                                                                                   
                                                      0         Ip
                                                  =2                                                   ,
                                                        Iq    0q×p         0p×p        |Λ̂+ |ÛT+ U−
       p×q           
         0        Ip
where                   is an orthogonal matrix and hence its spectral norm is one. Using the sub-
           Iq    0q×p
multiplicativity of spectral norm, we get
                                          n                              o
       |Λ̂| Ip,q ÛT U − ÛT UIp,q   ≤ 2max |Λ̂+ |ÛT+ U− , |Λ̂− |ÛT− U+ .

Now, note that (using Proof of Lemma C.4 in Section C.1 of Agterberg et al. (2022)),
                                                                               
     UT− Û+ |Λ̂+ | = M− ◦ UT− (B̂ − B)Û+ , UT+ Û− |Λ̂− | = M+ ◦ UT+ (B̂ − B)Û− ,

where
                                       !                                                      !
                      |λ̂j,+ |                                                 |λ̂j,− |
      M− =                                               , M+ =                                                  .
                λ̂j,+ − λi,−               i∈[q],j∈[q]
                                                                         λ̂j,− − λi,+              i∈[p],j∈[p]

Observe that, by submultiplicativity of spectral norm in Hadamard product and by Triangle in-
equality,
                       n                                                        o
 UT+ Û− |Λ̂− | ≤ ∥M+ ∥ UT+ (B̂ − B)U− UT− Û− + UT+ (B̂ − B)(In − U− UT− )Û−
                       n                                             o
                ≤ ∥M+ ∥ UT+ (B̂ − B)U− + B̂ − B sinΘ(U− , Û− )        [since U− , Û− ∈ O(n, d)]
                       n                                           o
                ≤ ∥M+ ∥ UT (B̂ − B)U + B̂ − B sinΘ(U− , Û− )



                                                                          13
```

## Page 14

```text
where the last line follows because UT+ (B̂ − B)U− is a submatrix of UT (B̂ − B)U. Similarly, we
can obtain,
                              n                                             o
      UT− Û+ |Λ̂+ | ≤ ∥M− ∥ UT (B̂ − B)U + B̂ − B sinΘ(U+ , Û+ ) .

Combining the above two inequalities, we get
                            
 |Λ̂| Ip,q ÛT U − ÛT UIp,q
                          n                                                                                              o
≤ 2max {∥M− ∥ , ∥M+ ∥} UT (B̂ − B)U + B̂ − B sinΘ(U− , Û− ) + B̂ − B                                  sinΘ(U+ , Û+ )
                                                       
                                             4        2
≤ 2max {∥M− ∥ , ∥M+ ∥} UT (B̂ − B)U +          B̂ − B
                                             λ

                                                                                                            2∥B̂−B∥
because from Davis Kahan theorem ( of Chen et al. (2021)),                          sinΘ(U+ , Û+ )     ≤       λ   ,
                             2∥B̂−B∥
 sinΘ(U− , Û− ) ≤               λ   .
From Weyl’s inequality, |λ̂j,+ − λj,+ | ≤ B̂ − B , and if r = ω(n3 ), then B̂ − B can be arbitrarily
small for sufficiently large n and r, with high probability. Thus, for sufficiently large n and r, with
high probability,

      λ̂j,+ > 0 for all j ∈ [d] =⇒ 0 < (M− )ij < 1 for all i, j ∈ [d] =⇒ ∥M− ∥ < d.

Similarly, it can be shown that, for sufficiently large n and r, ∥M+ ∥ < d. Thus, for sufficiently large
n and r, with high probability,
                                            (  1 −δ         1−2δ )
            
                   T      T
                                               n3 2        4 n3
       |Λ̂| Ip,q Û U − Û UIp,q      ≤ 2d               +               .
                                                 r         λ r




Lemma 2. In our setting, assume that for all i, j, γij = O(1) and r = ω(n3 ).                                 Define
H ∈ Rd×d such that for all k, l ∈ [d],
                         1
      Hkl =          1             1   .
                 |λl | + |λ̂k | 2
                     2



Then, for sufficiently large n and r, with high probability,
                  √ !
                    2       d
     ∥H∥ ≤          √     p .
                1+ 2         |λ|

Proof. Using Triangle Inequality and Weyl’s Inequality,

      |λk | − |λ̂k | ≤ |λk − λ̂k | ≤ B − B̂ .

Thus, |λ̂k | ≥ |λk | − B − B̂ . Recall that from Corollary 2, for sufficiently large n, r, B̂ − B < |λ|
                                                                                                     2

with high probability. Thus, for sufficiently large n, r, |λ̂k | ≥ |λ|
                                                                    2 with high probability.
Thus, for sufficiently large n, r, with high probability,
                         1
      Hkl ≤                  q         for all k, l ∈ [d]
                     1           |λ|
                 |λ| +
                     2
                                  2
                                  √            !
                                       2            d
       =⇒ ∥H∥ ≤                        √           p .
                             1+            2        |λ|




Lemma 3. In our setting, suppose r = ω(n3 ).                        Then, for sufficiently large n and r, with
high probability,
            −1        2
       Λ̂        ≤       .
                     |λ|

                             −1
Proof. Note that Λ̂               = diag( λ̂1 , . . . λ̂1 ). We know (see proof of Lemma 2 ), for sufficiently large n
                                                   1      d




                                                              14
```

## Page 15

```text
and r, for every k ∈ [d], |λ̂k | ≥ |λ|
                                    2 with high probability. Thus, for sufficiently large n and r, with
high probability,
            −1            1            2
       Λ̂        = min            ≤       .
                  k∈[d] |λ̂k |        |λ|



Lemma 4. In our setting, suppose r = ω(n3 ). Then for sufficiently large n and r, with
high probability,
                                  √      (           3  12 −δ      1−2δ )
         T        1     1
                            T       2  d             n            8d n3
       Û U|Λ| 2 − |Λ̂| 2 Û U ≤    √ √    (1 + 2d)             +             .
                                 1+ 2 λ               r           λ  r

Proof. Following Section C.1 in Agterberg et al. (2022),
                   1          1                           1         1
       ÛT U|Λ| 2 − |Λ̂| 2 ÛT U = ÛT U|Λ| 2 Ip,q − |Λ̂| 2 ÛT UIp,q
                                                              1     1
                                              = ÛT UIp,q |Λ| 2 − |Λ̂| 2 ÛT UIp,q
                                                    n                                          o
                                              = H ◦ ÛT (B̂ − B)U + |Λ̂| Ip,q ÛT U − ÛT UIp,q
                                                    n                                              o
                                              ≤ ∥H∥ ÛT (B̂ − B)U + |Λ̂| Ip,q ÛT U − ÛT UIp,q        .

Now, note that

       ÛT (B̂ − B)U ≤ ÛT UUT (B̂ − B)U + ÛT (I − UUT )(B̂ − B)U

                           ≤ UT (B̂ − B)U + sinΘ(Û, U)                  B̂ − B .

Observe that by Davis Kahan theorem (Chen et al., 2021), sinΘ(Û, U) ≤ λ1 B̂ − B .
For sufficiently large n and r, with high probability,
                                                           √ !
                                                             2       d
                                                  ∥H∥ ≤      √     √ ,
                                                          1+ 2        λ
                                                             3  12 −δ
                                                              n
                                           ÛT (B̂ − B)U ≤              ,
                                                               r
                                          (  1 −δ        1−2δ )
            
                   T       T
                                             n3 2       4 n3
       |Λ̂| Ip,q Û U − Û UIp,q     ≤ 2d              +                .
                                              r          λ r

Thus, for sufficiently large n and r, with high probability,
                                      √        (           3  12 −δ       3 1−2δ )
                 1       1              2    d               n          8d  n
       ÛT U|Λ| 2 − |Λ̂| 2 ÛT U ≤      √ √      (1 + 2d)             +                .
                                    1+ 2 λ                   r          λ    r

Lemma 5. In our setting, suppose r = ω(n3 ). Then, for sufficiently large n and r, with high
probability,
                                            (         3  12 −δ     √              1−2δ )
   T       − 12     − 12    T       1   2d       √     n            4 2 + 8(1 + d) n3
 Û U|Λ| Ip,q − |Λ̂| Ip,q Û U ≤     √ 3 (3 + 2)                 +                           .
                                 1 + 2 λ2               r                  λ         r

Proof. First note that (from proof of Lemma C.4 in Agterberg et al. (2022)),
             1              1                    1
                                                        1                                1
                                                                                                     1
   ÛT U|Λ|− 2 Ip,q − |Λ̂|− 2 Ip,q ÛT U = |Λ̂|− 2 Ip,q |Λ̂| 2 Ip,q ÛT U − ÛT UIp,q |Λ| 2 Ip,q |Λ|− 2 .
                                                                                 1
                                                                                        √
Now, for sufficiently large n and r, with high probability,                |Λ̂|− 2   ≤ √ 2 (following the same
                                                                                         |λ|
strategy as proof of Lemma 3 ).
Thus, for sufficiently large n and r, with high probability,
                                        √
    T     − 12          − 12    T         2        1                            1
 Û U|Λ| Ip,q − |Λ̂| Ip,q Û U ≤              |Λ̂| 2 Ip,q ÛT U − ÛT UIp,q |Λ| 2
                                        √λ n
                                          2          1                                   1                           1
                                                                                                                         o
                                      ≤         |Λ̂| 2 (Ip,q ÛT U − ÛT UIp,q ) + |Λ̂| 2 ÛT UIp,q − ÛT UIp,q |Λ| 2 .
                                        √λ                                        √
                                          2                                         2      1                           1
                                      ≤ 3 |Λ̂|(Ip,q ÛT U − ÛT UIp,q ) +             |Λ̂| 2 ÛT UIp,q − ÛT UIp,q |Λ| 2
                                        λ 2                                        λ
                                                       (            3  12 −δ     √                1−2δ )
                                            1     2d           √     n            4 2 + 8(1 + d) n3
                                      ≤      √ 3 (3 + 2)                       +                                .
                                        1 + 2 λ2                      r                 λ             r




                                                              15
```
