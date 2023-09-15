open import Data.Nat
open import Data.Fin hiding (_+_ ; _-_)

top : {N : ℕ} -> Fin (suc N)
top {zero} = zero
top {suc N} = suc top

+1 : {N : ℕ} -> Fin N -> Fin (suc N)
+1 zero = suc zero
+1 (suc n) = suc (+1 n)

wkn-under-binder : {N : ℕ} -> Fin (suc N) -> Fin (suc (suc N))
wkn-under-binder zero = zero
wkn-under-binder (suc zero) = suc (suc zero)
wkn-under-binder (suc (suc x)) = suc (suc (+1 x))

subst : ℕ -> ℕ -> Set
subst N M = Fin N -> Fin M

identity : {N : ℕ} -> subst N N
identity {N} = λ x → x

top:=_ : {N : ℕ} -> Fin N -> subst (suc N) N
top:=_ y zero = y
top:=_ y (suc x) = x

-- _:=_ : {N : ℕ} -> Fin N -> Fin N -> subst N  N
-- (z := y) x with x == z
-- ... | tt = y
-- ... | ff = z

wkn-subst : {N M : ℕ} -> subst N M -> subst (suc N) (suc M)
wkn-subst σ zero = zero
wkn-subst σ (suc x) = suc (σ x)

wkn-subst-under-binder : {N : ℕ} -> subst (suc N) (suc (suc N))
wkn-subst-under-binder = wkn-under-binder


data proc (N : ℕ) :  Set where
  ∅ : proc N
  _!_∙_ : Fin N -> Fin N -> proc N -> proc N
  _？[]·_ : Fin N -> proc (suc N) -> proc N
  _∣_ : proc N -> proc N -> proc N
  [ν]_ : proc (suc N) -> proc N
  _++_ : proc N -> proc N -> proc N

_[_] : {N M : ℕ} -> proc N -> subst N M -> proc M
_[_] ∅ σ = ∅
_[_] (x ! y ∙ P) σ = σ x ! σ y ∙ (P  [ σ ])
_[_] (x ？[]· P) σ = σ x ？[]· (P [ {!!} ]) -- compose +1 and σ
_[_] (P ∣ Q) σ = (P [ σ ]) ∣ (Q [ σ ])
_[_] ([ν] P) σ = [ν] (P [ wkn-subst σ ])
_[_] (P ++ Q) σ = (P [ σ ]) ++ (Q [ σ ])

data bind : Set where
  no-var : bind
  1-var : bind

data action (N : ℕ) : bind -> Set where
  _!_ : Fin N -> Fin N -> action N no-var
  _？_ : Fin N -> Fin N -> action N no-var
  _![] : Fin N -> action N 1-var
  τ : action N no-var

-- this function shows which actions will create a new name
#n : {N : ℕ} {B : bind} -> action N B -> ℕ
#n {_} {no-var} _ = zero
#n {_} {1-var} _ = 1

s#α : {N : ℕ} {B : bind} -> (α : action N B) -> subst N (#n α + N)
s#α {_} {no-var} α = identity
s#α {_} {1-var} α = +1

data _-_⟶_ {N : ℕ} : {B : bind} -> proc N -> (α : action N B) -> proc (#n α + N) -> Set where
  step-out : (x y : Fin N) -> (P : proc N) ->
    (x ! y ∙ P) - x ! y ⟶ P

  step-in : (x y z : Fin N) -> (P : proc (suc N)) ->
    (x ？[]· P) - x ？ y ⟶  (P [ top:= y ])

  step-par-l : {B : bind} -> (x y : Fin N) ->  (P Q : proc N) -> (α : action N B) -> (P' : proc (#n α + N)) ->
    P - α ⟶ P' ->
    (P ∣ Q) - α ⟶ (P' ∣ (Q [ s#α α ]))

--   -- step-par-r

  step-comm-l : (x y : Fin N) -> (P Q P' Q' : proc N) ->
    P - x ! y ⟶ P' ->
    Q - x ？ y ⟶ Q' ->
    (P ∣ Q) - τ ⟶ (P' ∣ Q')

  step-comm-r : (x y : Fin N) -> (P Q P' Q' : proc N) ->
    P - x ？ y ⟶ P' ->
    Q - x ! y ⟶ Q' ->
    (P ∣ Q) - τ ⟶ (P' ∣ Q')


  step-sum-l : {B : bind} -> (P Q : proc N) -> (α : action N B) -> (P' : proc (#n α + N)) ->
    P - α ⟶ P' ->
    (P ++ Q) - α ⟶ P'

  step-sum-r : {B : bind} -> (P Q : proc N) -> (α : action N B) -> (Q' : proc (#n α + N)) ->
    Q - α ⟶ Q' ->
    (P ++ Q) - α ⟶ Q'

  step-open : (x : Fin N) (P : proc (suc N))(P' : proc (suc N)) ->
    P - (+1 x) ! top ⟶ P' ->
    ([ν] P) - x ![] ⟶ P'

  step-close-l : (P Q Q' : proc N) -> (P' : proc (suc N)) ->

    (P ∣ Q) - τ ⟶ (([ν] P') ∣ Q')
