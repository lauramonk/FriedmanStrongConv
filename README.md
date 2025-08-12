# Formalizing Friedman's theorem in Lean 4 using strong convergence

The aim of this project is to formalize a result related to the expansion of large random regular graphs, conjectured by [Alon](https://link.springer.com/article/10.1007/BF02579166) in 1986 and first proven by [Friedman](https://dl.acm.org/doi/10.1145/780542.780646) in 2003. The historical proof of this celebrated result is very long and presents several challenges. However, in a recent breakthrough, [Chen, Garza-Vargas, Tropp and van Handel](https://arxiv.org/abs/2405.16026) provided a radically new approach to this class of problems, which allows to prove Friedman's theorem in a very concise self-contained proof. We hope to formalize this new proof, following [van Handel's survey](https://web.math.princeton.edu/~rvan/cdm250630.pdf).

## The spectrum of $d$-regular graphs

Let $d \geq 3$ be a fixed integer. A $d$-regular graph is a finite graph $G=(V,E)$, non-oriented, possibly with loops and muli-edges, such that every vertex has exactly $d$ neighbours. If the graph has $n$ vertices, then the adjacency matrix $A$ of the graph is a $n \times n$ matrice with the entry of coordinates $(i,j)$ counting edges from $i$ to $j$. This real symmetrix matrix is diagonalizable and its $n$ eigenvalues are all included in the segment $[-d,d]$. We denote them as $\lambda_1 \geq \lambda_2 \geq \ldots \geq \lambda_n$, counting multiplicities.

The first eigenvalue $\lambda_1$ is always equal to $d$; this is the eigenvalue corresponding to constant eigenvectors. The second eigenvalue is equal to $d$ if and only if the graph is disconnected. The last eigenvalue $\lambda_n$ is equal to $-d$ if and only if the graph is bipartite, i.e. we can split the vertices $V = V_1 \sqcup V_2$ so that every edge of $G$ has one endpoint in $V_1$ and the other in $V_2$.

The quantity at the heart of this project is the *spectral gap* of the graph, defined as the spacing between the trivial eigenvalue $d$ and
$$\lambda_+ := \max_{2 \leq i \leq n} |\lambda_i| \leq d.$$
This spacing measures the connectivity of the graph, the speed of convergence of random walks.

As the graph grows, the size of the spectral gap is limited by the Alon-Boppana bound, which states that
$$\lambda_2 \geq 2 \sqrt{d-1}
 - \frac{2 \sqrt{d-1}-1}{\lfloor \mathrm{diam}(G) /2 \rfloor}$$
where $\mathrm{diam}(G)$ is the diameter of $G$. As the number of vertices $n$ goes to infinity, we obtain that $\lambda_+ \geq 2 \sqrt{d-1} - o(1)$. The value $2 \sqrt{d-1}$ appears here in relation to the spectrum of the infinite $d$-regular tree.

## Random $d$-regular graphs
