import Lazylist.impl
import Lean

macro:max "prod_of!" n:num : term =>
  match n.getNat with
  | 0 => ``(())
  | 1 => ``(id)
  | n + 2 =>
    ``((· , ·)) >>= n.foldM fun _ _ a =>
      ``((· , $a))

/--
  Similar to Haskell's `MonadZip`, but for collections especially.
  But relaxes on the constraint that `m` must be a `Monad` first.
  - Any `Monad` is `Zippable`.
-/
class Zippable (m : Type u -> Type v) where

  /-- `zipWith` zips 2 collections while simultaneously applying a function (which should be curried) to each pair. -/
  zipWith (f : α -> β -> γ) : m α -> m β -> m γ
  /-- `zipWith3` zips 3 collections while simultaneously applying a function (which should be curried) to each 3-tuple. -/
  zipWith3 (f : α -> β -> γ -> δ) : m α -> m β -> m γ -> m δ
  /-- `zipWith4` zips 4 collections while simultaneously applying a function (which should be curried) to each 4-tuple. -/
  zipWith4 (f : α -> β -> γ -> δ -> ζ) : m α -> m β -> m γ -> m δ -> m ζ
  /-- `zipWith5` zips 5 collections while simultaneously applying a function (which should be curried) to each 5-tuple. -/
  zipWith5 (f : α -> β -> γ -> δ -> ζ -> η) : m α -> m β -> m γ -> m δ -> m ζ -> m η
  /-- `zipWith6` zips 6 collections while simultaneously applying a function (which should be curried) to each 6-tuple. -/
  zipWith6 (f : α -> β -> γ -> δ -> ζ -> η -> θ) : m α -> m β -> m γ -> m δ -> m ζ -> m η -> m θ
  /-- `zipWith7` zips 7 collections while simultaneously applying a function (which should be curried) to each 7-tuple. -/
  zipWith7 (f : α -> β -> γ -> δ -> ζ -> η -> θ -> ι) : m α -> m β -> m γ -> m δ -> m ζ -> m η -> m θ -> m ι

  /-- `zip` zips 2 collections and terminates on the shorter one and discards the rest of the longer one. -/
  zip : m α -> m β -> m (α × β) := zipWith prod_of! 2
  /-- `zip3` zips 3 collections and terminates on the shortest one and discards the rest of the others. -/
  zip3 : m α -> m β -> m γ -> m (α × β × γ) := zipWith3 prod_of! 3
  /-- `zip4` zips 4 collections and terminates on the shortest one and discards the rest of the others. -/
  zip4 : m α -> m β -> m γ -> m δ -> m (α × β × γ × δ) := zipWith4 prod_of! 4
  /-- `zip5` zips 5 collections and terminates on the shortest one and discards the rest of the others. -/
  zip5 : m α -> m β -> m γ -> m δ -> m ε -> m (α × β × γ × δ × ε) := zipWith5 prod_of! 5
  /-- `zip6` zips 6 collections and terminates on the shortest one and discards the rest of the others. -/
  zip6 : m α -> m β -> m γ -> m δ -> m ε -> m ζ -> m (α × β × γ × δ × ε × ζ) := zipWith6 prod_of! 6
  /-- `zip7` zips 7 collections and terminates on the shortest one and discards the rest of the others. -/
  zip7 : m α -> m β -> m γ -> m δ -> m ε -> m ζ -> m η -> m (α × β × γ × δ × ε × ζ × η) := zipWith7 prod_of! 7

section
variable
  {α : Type u₁} {β : Type u₂} {γ : Type u₃} {δ : Type u₄}
  {ζ : Type u₅} {η : Type u₆} {θ : Type u₇} {ι : Type u₈}

namespace List
def zipWith3 (f : α -> β -> γ -> δ) : List α -> List β -> List γ -> List δ := go #[] where
  go acc
  | a :: as, b :: bs, c :: cs => go (acc.push $ f a b c) as bs cs
  | _, _, _ => acc.toList
def zipWith4 (f : α -> β -> γ -> δ -> ζ) : List α -> List β -> List γ -> List δ -> List ζ := go #[] where
  go acc
  | a :: as, b :: bs, c :: cs, d :: ds => go (acc.push $ f a b c d) as bs cs ds
  | _, _, _, _ => acc.toList
def zipWith5 (f : α -> β -> γ -> δ -> ζ -> η) : List α -> List β -> List γ -> List δ -> List ζ -> List η := go #[] where
  go acc
  | a :: as, b :: bs, c :: cs, d :: ds, e :: es => go (acc.push $ f a b c d e) as bs cs ds es
  | _, _, _, _, _ => acc.toList
def zipWith6 (f : α -> β -> γ -> δ -> ζ -> η -> θ) : List α -> List β -> List γ -> List δ -> List ζ -> List η -> List θ := go #[] where
  go acc
  | a :: as, b :: bs, c :: cs, d :: ds, e :: es, f' :: fs => go (acc.push $ f a b c d e f') as bs cs ds es fs
  | _, _, _, _, _, _ => acc.toList
def zipWith7 (f : α -> β -> γ -> δ -> ζ -> η -> θ -> ι) : List α -> List β -> List γ -> List δ -> List ζ -> List η -> List θ -> List ι := go #[] where
  go acc
  | a :: as, b :: bs, c :: cs, d :: ds, e :: es, f' :: fs, g :: gs => go (acc.push $ f a b c d e f' g) as bs cs ds es fs gs
  | _, _, _, _, _, _, _ => acc.toList
attribute [inline] zipWith3 zipWith4 zipWith5 zipWith6 zipWith7
end List

open List in instance : Zippable List where
  zipWith; zipWith3; zipWith4; zipWith5; zipWith6; zipWith7


def minOfI [Min α] : (l : List α) -> l ≠ [] -> α
  | x :: xs, _ => xs.foldl min x
@[implemented_by minOfI, reducible] def minOf [Min α] : (l : List α) -> l ≠ [] -> α
  | [x], _ => x
  | x :: y :: xs, _ => min x $ minOf (y :: xs) (List.cons_ne_nil _ _)

-- with respect to Lisp's isonymic functions.
-- (min (min (min ..))) ≅ (cons (cons (cons ..))) and
-- in the case below interspersed by the transitive fact of `(· <= ·)`

private abbrev cdr {a b} := Nat.min_le_right a b
private abbrev car {a b} := Nat.min_le_left  a b
private abbrev nonempty {a : α} {l : List α} := List.cons_ne_nil a l
local infixr:60 " <> " => Nat.le_trans
local macro "cadr" : term => ``(cdr <> car)
local macro "caddr" : term => ``(cdr <> cdr <> car)
local macro "cadddr" : term => ``(cdr <> cdr <> cdr <> car)
local macro "caddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> car)
local macro "cadddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> cdr <> car)
local macro "caddddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> cdr <> cdr <> car)
local macro "cadddddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> cdr <> cdr <> cdr <> car)

local macro "cddr" : term => ``(cdr <> cdr)
local macro "cdddr" : term => ``(cdr <> cdr <> cdr)
local macro "cddddr" : term => ``(cdr <> cdr <> cdr <> cdr)
local macro "cdddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> cdr)
local macro "cddddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> cdr <> cdr)
local macro "cdddddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> cdr <> cdr <> cdr)
local macro "cddddddddr" : term => ``(cdr <> cdr <> cdr <> cdr <> cdr <> cdr <> cdr <> cdr)

open Lean
private abbrev accessors : Array $ MacroM Term :=
  #[ `(car), `(cadr), `(caddr), `(cadddr)
  , `(caddddr), `(cadddddr), `(caddddddr), `(cadddddddr)]
private abbrev accessors' : Array $ MacroM Term :=
  #[ `(cdr), `(cddr), `(cdddr), `(cddddr)
   , `(cdddddr), `(cddddddr), `(cdddddddr), `(cddddddddr)]
private def pfcmds (s : Ident) (pf : Term) (cont : Term) : MacroM Term :=
  `(have : m <= Array.size $s := $pf; $cont)
@[local simp] private theorem accsize  :  accessors.size = 8 := by decide
@[local simp] private theorem accsize' : accessors'.size = 8 := by decide

local syntax "proof_and_fold!" ident ident+ : term
macro_rules
  | `(proof_and_fold! $f $[$t]*) => do
      let ts := t.size
      if H : ts <= 8 ∧ ts >= 2 then
        let funapp <- t.foldlM (init := f) fun a s => `($a ($s[i]))
        let cont <- `(Nat.fold m (init := #[]) fun i h a => Array.push a $(funapp))
        let blk <- ts.foldRevM (init := cont) fun i h a => do
          have : i < accessors.size := Nat.lt_of_lt_of_le h $ accsize ▸ H.1
          if i = ts - 1 then
            have : i - 1 < accessors'.size := Nat.sub_lt_of_lt $ accsize' ▸ accsize ▸ this
            pfcmds t[i] (<-accessors'[i-1]) a
          else
            pfcmds t[i] (<- accessors[i]) a
        `(let m := minOf [$[Array.size $t],*] nonempty;
          $blk)
      else Macro.throwError "handler not implemented, see source."

namespace Array
def zipWith3 (f : α -> β -> γ -> δ) : Array α -> Array β -> Array γ -> Array δ
  | as, bs, cs => proof_and_fold! f as bs cs
def zipWith4 (f : α -> β -> γ -> δ -> ζ) : Array α -> Array β -> Array γ -> Array δ -> Array ζ
  | as, bs, cs, ds => -- what `proof_and_fold!` should be expanded to
    let m := minOf [as.size, bs.size, cs.size, ds.size] nonempty
    have h₁ : m <= as.size := car
    have : m <= bs.size := cadr
    have : m <= cs.size := caddr
    have : m <= ds.size := cdddr
    m.fold (init := #[]) fun i h a => a.push (f (as[i]'(h <> h₁)) bs[i] cs[i] ds[i])
def zipWith5 (f : α -> β -> γ -> δ -> ζ -> η) : Array α -> Array β -> Array γ -> Array δ -> Array ζ -> Array η
  | as, bs, cs, ds, es => proof_and_fold! f as bs cs ds es
def zipWith6 (f : α -> β -> γ -> δ -> ζ -> η -> θ) : Array α -> Array β -> Array γ -> Array δ -> Array ζ -> Array η -> Array θ
  | as, bs, cs, ds, es, fs => proof_and_fold! f as bs cs ds es fs
def zipWith7 (f : α -> β -> γ -> δ -> ζ -> η -> θ -> ι) : Array α -> Array β -> Array γ -> Array δ -> Array ζ -> Array η -> Array θ -> Array ι
  | as, bs, cs, ds, es, fs, gs => proof_and_fold! f as bs cs ds es fs gs
attribute [inline] zipWith3 zipWith4 zipWith5 zipWith6 zipWith7
end Array

open Array in instance : Zippable Array where
  zipWith; zipWith3; zipWith4; zipWith5; zipWith6; zipWith7

namespace LazyList
def zipWith3 (f : α -> β -> γ -> δ) : LazyList α -> LazyList β -> LazyList γ -> LazyList δ
  | a ::' as, b ::' bs, c ::' cs => f a b c ::' zipWith3 f as.get bs.get cs.get
  | _, _, _ => [||]
def zipWith4 (f : α -> β -> γ -> δ -> ζ) : LazyList α -> LazyList β -> LazyList γ -> LazyList δ -> LazyList ζ
  | a ::' as, b ::' bs, c ::' cs, d ::' ds => f a b c d ::' zipWith4 f as.get bs.get cs.get ds.get
  | _, _, _, _ => [||]
def zipWith5 (f : α -> β -> γ -> δ -> ζ -> η) : LazyList α -> LazyList β -> LazyList γ -> LazyList δ -> LazyList ζ -> LazyList η
  | a ::' as, b ::' bs, c ::' cs, d ::' ds, e ::' es => f a b c d e ::' zipWith5 f as.get bs.get cs.get ds.get es.get
  | _, _, _, _, _ => [||]
def zipWith6 (f : α -> β -> γ -> δ -> ζ -> η -> θ) : LazyList α -> LazyList β -> LazyList γ -> LazyList δ -> LazyList ζ -> LazyList η -> LazyList θ
  | a ::' as, b ::' bs, c ::' cs , d ::' ds, e ::' es, f' ::' fs => f a b c d e f' ::' zipWith6 f as.get bs.get cs.get ds.get es.get fs.get
  | _, _, _, _, _, _ => [||]
def zipWith7 (f : α -> β -> γ -> δ -> ζ -> η -> θ -> ι) : LazyList α -> LazyList β -> LazyList γ -> LazyList δ -> LazyList ζ -> LazyList η -> LazyList θ -> LazyList ι
  | a ::' as, b ::' bs, c ::' cs, d ::' ds, e ::' es, f' ::' fs, g ::' gs => f a b c d e f' g ::' zipWith7 f as.get bs.get cs.get ds.get es.get fs.get gs.get
  | _, _, _, _, _, _, _ => [||]
end LazyList

open LazyList in instance : Zippable LazyList where
  zipWith; zipWith3; zipWith4; zipWith5; zipWith6; zipWith7

instance (priority := low) [Monad m] : Zippable m where
  zipWith  := (· <$> · <*> ·)
  zipWith3 := (· <$> · <*> · <*> ·)
  zipWith4 := (· <$> · <*> · <*> · <*> ·)
  zipWith5 := (· <$> · <*> · <*> · <*> · <*> ·)
  zipWith6 := (· <$> · <*> · <*> · <*> · <*> · <*> ·)
  zipWith7 := (· <$> · <*> · <*> · <*> · <*> · <*> · <*> ·)

end
