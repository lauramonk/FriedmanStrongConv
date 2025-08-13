# Formalizing Friedman's theorem in Lean 4 using strong convergence

The aim of this project is to formalize a result related to the expansion of large random regular graphs, conjectured by [Alon](https://link.springer.com/article/10.1007/BF02579166) in 1986 and first proven by [Friedman](https://dl.acm.org/doi/10.1145/780542.780646) in 2003. The historical proof of this celebrated result is very long and presents several challenges. However, in a recent breakthrough, [Chen, Garza-Vargas, Tropp and van Handel](https://arxiv.org/abs/2405.16026) provided a radically new approach to this class of problems, which allows to prove Friedman's theorem in a very concise self-contained proof. We hope to formalize this new proof, following [van Handel's survey](https://web.math.princeton.edu/~rvan/cdm250630.pdf).

## The spectrum of $d$-regular graphs

Let $d \geq 3$ be a fixed integer. A $d$-regular graph is a finite graph $G=(V,E)$, non-oriented, possibly with loops and muli-edges, such that every vertex has exactly $d$ neighbours. If the graph has $n$ vertices, then the adjacency matrix $A$ of the graph is a $n \times n$ matrice with the entry of coordinates $(i,j)$ counting edges from $i$ to $j$. This real symmetrix matrix is diagonalizable and its $n$ eigenvalues are all included in the segment $[-d,d]$. We denote them as $\lambda_1 \geq \lambda_2 \geq \ldots \geq \lambda_n$, counting multiplicities.

The first eigenvalue $\lambda_1$ is always equal to $d$; this is the eigenvalue corresponding to constant eigenvectors. The second eigenvalue is equal to $d$ if and only if the graph is disconnected. The last eigenvalue $\lambda_n$ is equal to $-d$ if and only if the graph is bipartite, i.e. we can split the vertices $V = V_1 \sqcup V_2$ so that every edge of $G$ has one endpoint in $V_1$ and the other in $V_2$.

The quantity at the heart of this project is the *spectral gap* of the graph, defined as the spacing between the trivial eigenvalue $d$ and
$\lambda_+ := \max_{2 \leq i \leq n} |\lambda_i| \leq d$.
This spacing measures the connectivity of the graph, the speed of convergence of random walks.

As the graph grows, the size of the spectral gap is limited by the Alon-Boppana bound, which states that
$\lambda_2 \geq 2 \sqrt{d-1} - o(1)$ as $n \rightarrow \infty$. The value $2 \sqrt{d-1}$ appears here in relation to the spectrum of the infinite $d$-regular tree.

## Random $d$-regular graphs

The Alon conjecture states that "almost all" large $d$-regular graphs satisfy $\lambda_+ \leq 2 \sqrt{d-1} + o(1)$ as their size $n$ goes to infinity. To make this informal statement into a theorem, one can equip the set of $d$-regular graphs with $n$ vertices with a probability measure; several such measures exist. In 2002, after 20 years of harduous research, Friedman proved for several models of random graphs that, for all $\epsilon > 0$, the probability that $\lambda_+ \leq 2 \sqrt{d-1} + \epsilon$ goes to $1$ as $n$ goes to $\infty$.

For the purpose of this formalization project, we suggest to restrict the attention to one specific model of random $d$-regular graphs, as done in van Ramon's survey. More precisely, we assume that $d = 2s \geq 4$ is even. We fix the vertex set to be $V = \{1, \ldots, n\}$. We pick $s$ random permutations of $V$, denoted as $\sigma_1, \ldots, \sigma_s$, i.i.d. uniformly. We then obtain a random $d$-regular graph by connecting $v$ and $\sigma_i(v)$ for all $v \in V$ and $1 \leq i \leq s$. (Note that the resulting graph has self-loops and multi-edges a priori, which explains the necessity to use the Graph library in Mathlib as opposed to SimpleGraph). In this setting, the new approach to strong convergence allows to prove Friedman's theorem very efficiently, which is what we hope to achieve. This will still require a lot of work, with elements of various complexity; I believe it will be the opportunity to add many interesting mathematical tools and concepts to Mathlib.
