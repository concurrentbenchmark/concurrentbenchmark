This is a ripoff (with minor adaptations by AM) from the Abella library as
originally authored by Miller & Tiu

 Proof Search Specifications of Bisimulation and Modal Logics for the π-calculus, by Alwen Tiu and Dale Miller. ACM Transactions on Computational Logic. 

To quote
%% A specification of the late transition system for the finite pi calculus.
%% Given that the meta-logic of Abella is intuitionistic, the
%% specification of bisimulation here corresponds to open bisimulation.

==> so, needs to be ported to strong barbed


Notes on the challenge (wrt open bisimulation)

reflexivity: much simpler to prove coinductively (3
cases). Inductively would need induction over processes
(currently broken)

transitivity literally same proof (ind vs coind)

symmetry comes from mere case analysis

what is scary is: the coinductive equivalence relation proof does not use anything
of the LTS: it may as well be abstract!