import Lean
import Lazylist.zippable
namespace LazyList open Lean

local macro f:term:50 " depends_on! " p:term:50 : term =>
  `(if $p then Option.some $f else Option.none)

/--
  The notation for generic comprehension (applies to collections, monads etc).
  - Available for any datatype that implements `Functor`, with some functionalities
    requiring additional typeclass (listed below).
  - Any usage of filtering (`where` clause) requires an additional `Mappable` instance.
  - This module includes various instance of `Mappable` `Zippable` `Monad` for `Array` `List`.
  - The RHS of each equation listed below is a close representation of the actual translation.
  There are 2 types of comprehension available:
  1. the naive one: `[f <- l, p] = l.map f <| l.filter p`;
  2. the more _advanced_ one, similar to that of Haskell `(pat <- term)+`:
    - nondeterministic search (non-sequential binding).
      - Additionally requires `Seq` instance.
      - **Syntax** `[term (where pred)? | (pat <- term,)+]`
      ```
      [(x, y, z) where x + y = z | (x, _) <- [|...|]
                                 , (_, y) <- [|...|]
                                 , (z, _) <- [|...|]]
      = filterMap id $
          (fun (x, _) (_, y) (z, _) =>
            if x + y = z then some (x, y, z)) else none)
          <$> [|...|] <*> [|...|] <*> [|...|]
      ```
    - **Preferrable** due to better predicative filtering for _non-lazy_ structures,
      but may encounter surprising issues of universe level inferring, see notes below.
      The _canonical_ nondeterministic search with sequential binding with respect to Haskell.
      (i.e. `x` is bound in `ys` in `x <- xs in y <- ys` but not in `x <- xs, y <- ys`).
      - Additionally requires `Bind` instance.
      - **Syntax** `[term (where pred)? | (pat <- term in)+]`
      ```
      [(x, y, z) where x + y = z | (x, _) <- [|...|]
                                in (_, y) <- [|...|]
                                in (z, _) <- [|...|]]
      = [|...|] >>= fun (x, _) =>
          [|...|] >>= fun (_, y) =>
            [|...|].filterMap fun (z, _) =>
              fun (x, _) (_, y) (z, _) =>
                if x + y = z then some (x, y, z)) else none
      ```
    - parallel comprehension. Additionally requires `Zippable` instance.
      - **Syntax** `[term (where pred)? | (pat <- term |)+]`
      ```
      [(x, y, z) where x + y = z | (x, _) <- [|...|]
                                 | (_, y) <- [|...|]
                                 | (z, _) <- [|...|]]
      = [|...|] <+> [|...|] <+> [|...|] |>.filterMap
          fun ((x, _), (_, y), (z, _)) =>
            if x + y = z then some (x, y, z) else none
      ```
  - **Note** In the case of _sequential_ nondeterministic search Lean may complain about unsolvable
    universe levels, even if the result type is obviously concrete. This is because of how the macro is implemented (see above) and
    right now: `fun (x, _) (_, y) => ...` `fun (x, _) => fun (_, y) => ...` behaves differently in terms of level inferring where
    it shouldn't, given the fact that they are definitionally equal.
    Normally RHS can be reduced to LHS which is in WHNF, but that is not the case if there's extra code between the two lambda binders in RHS,
    which, is exactly the case regarding our macro translation.
    This normalization process shouldn't mess with level solving but that is not the case right now.
    This is observed with
    ```
    set_option pp.universes true in section variable {α β γ δ ε σ τ}
    #check show α × δ -> ε × β -> γ × σ -> α × β × γ from
      λ (a, _) => λ (_, b) => λ (c, _) => (a, b, c)           -- The first one has explicit motive
    #check show α × δ -> ε × β -> γ × σ -> α × β × γ from
      λ (a, _) (_, b) (c, _) => (a, b, c)                     -- while the second one doesn't.
    end
    ```
    In that case you may need to explicitly provide type annotations e.g.
    ```
    show LazyList (Nat × Nat) from [(x, y) | (x, _) <- [|(1,2),(3,4)|] in (_, y) <- [|(5,6),(7,8)|]]
    ```
  e.g.
  ```
  -- calculates every pythagorean triples within [1, n]
  def pyth (n : Nat) : LazyList (Nat × Nat × Nat) :=
    [(x, y, z) where x ^ 2 + y ^ 2 == z ^ 2
      | x <- [|1 ~~ n + 1|]
     in y <- [|x ~~ n + 1|]
     in z <- [|y ~~ n + 1|]]

  #eval [x + y | x <- some 1, y <- none] -- none
  ```
-/
syntax (name := «term[|_<-_|]») "[" term " | " withoutPosition((term (" ← " <|> " <- ") term),+) "]" : term
syntax (name := «term[|_<-_?|]») "[" term " where"  term " | " withoutPosition((term (" ← " <|> " <- ") term),+) "]" : term

@[inherit_doc «term[|_<-_|]»] syntax "[" term (" ← " <|> " <- ") term (" , " term)? "]" : term

syntax (name := «term[|_<-_||]») (priority := 1002) "[" term " | " withoutPosition(sepBy1((term (" ← " <|> " <- ") term), " | ")) "]" : term
syntax (name := «term[|_<-_|?|]»)(priority := 1002) "[" term " where " term " | " withoutPosition(sepBy1((term (" ← " <|> " <- ") term), " | ")) "]" : term

@[inherit_doc gen] syntax "[|" term " ~~ " (term)? (" : " term)? "|]" : term
@[inherit_doc gen] syntax "[|" term " to " (term)? (" by " term)? "|]" : term

syntax (name := «term[|_<-_in|]») "[" term " | " withoutPosition(sepBy1((term (" ← " <|> " <- ") term), " in ")) "]" : term
syntax (name := «term[|_<-_in?|]») "[" term " where " term " | " withoutPosition(sepBy1((term (" ← " <|> " <- ") term), " in ")) "]" : term

attribute [inherit_doc «term[|_<-_|]»]  «term[|_<-_?|]» «term[|_<-_||]» «term[|_<-_|?|]» «term[|_<-_in|]» «term[|_<-_in?|]»

macro_rules
-- gen
  | `([| $start to $(stop)? $[by $step]? |]) => do
    ``([| $start ~~ $(stop)? $[: $step]? |])
  | `([| $start ~~ $(stop)? $[: $step]? |]) => do
    let stop <- if let .some e := stop then ``(Option.some $e) else ``(Option.none)
    let step <- if let .some e := step then pure e else ``(One.one)
    ``(LazyList.gen $start $stop $step)
-- naive
  | `([ $f <- $l $[, $p]? ]) => do
    match p with
    | none => ``(Functor.map $f $l)
    | some p =>
      let mf <- `(fun x => if $p x then Option.some ($f x) else Option.none)
      ``(Mappable.filterMap $mf $l)
  | `([ $f ← $l $[, $p]? ]) => ``([ $f <- $l $[, $p]? ])
-- nondeterministic search
  | `([ $f | $[$i <- $l],* ]) => do
    if h : l.size >= 1 then
      let is <- ``(fun $i* => $f)
      let fn <- ``(Functor.map $is)
      let l0 := l[0]
      show MacroM Term from
      ``($fn $l0) >>= l.foldlM (start := 1) fun a s =>
        ``(Seq.seq $a (fun _ : Unit => $s))
    else unreachable!
  | `([ $f | $[$i ← $l],* ]) => ``([ $f | $[$i <- $l],* ])
  | `([ $f where $p | $[$i <- $l],* ]) => do
    let mf <- ``($f depends_on! $p)
    ``(Mappable.filterMap id [ $mf | $[$i <- $l],* ])
  | `([ $f where $p | $[$i ← $l],* ]) => do
    ``([ $f where $p | $[$i <- $l],* ])
-- sequential binding version of the above
  | `([ $f | $[$i <- $l]in* ]) => do
    if h : i.size >= 1 ∧ l.size >= 1 then
      let (iz, lz) := (i[i.size - 1], l[l.size - 1])
      let li := (l.zip i)[:l.size - 1]
      show MacroM Term from
      ``(Functor.map (fun $iz => $f) $lz) >>= li.foldrM fun (t, fb) a =>
        ``(Bind.bind $t (fun $fb => $a))
    else unreachable!
  | `([ $f | $[$i ← $l]in* ]) => ``([ $f | $[$i <- $l]in* ])
  | `([ $f where $p | $[$i <- $l]in* ]) => do
    let mf <- `($f depends_on! $p)
    let (iz, lz) := (i[i.size - 1]!, l[l.size - 1]!)
    let li := (l.zip i)[:l.size - 1]
    show MacroM Term from
    ``(Mappable.filterMap (fun $iz => $mf) $lz) >>=
      li.foldrM fun (t, fb) a => ``(Bind.bind $t (fun $fb => $a))
  | `([ $f where $p | $[$i ← $l]in* ]) => ``([ $f where $p | $[$i <- $l]in* ])
-- parallel
  | `([ $f | $[$i <- $l]|* ]) => do
    match h : l.size with
    | 0 => unreachable!
    | 1 => ``(Functor.map       (fun $i* => $f) $(l[0]))
    | 2 => ``(Zippable.zipWith  (fun $i* => $f) $(l[0]) $(l[1]))
    | 3 => ``(Zippable.zipWith3 (fun $i* => $f) $(l[0]) $(l[1]) $(l[2]))
    | 4 => ``(Zippable.zipWith4 (fun $i* => $f) $(l[0]) $(l[1]) $(l[2]) $(l[3]))
    | 5 => ``(Zippable.zipWith5 (fun $i* => $f) $(l[0]) $(l[1]) $(l[2]) $(l[3]) $(l[4]))
    | 6 => ``(Zippable.zipWith6 (fun $i* => $f) $(l[0]) $(l[1]) $(l[2]) $(l[3]) $(l[4]) $(l[5]))
    | 7 => ``(Zippable.zipWith7 (fun $i* => $f) $(l[0]) $(l[1]) $(l[2]) $(l[3]) $(l[4]) $(l[5]) $(l[6]))
    | _ + 8 =>
      let i := i.map fun i => ⟨i.raw.setKind `term⟩
      let ls := l.size
      let hd <- ``(Zippable.zip7 $(l[ls - 7]) $(l[ls - 6]) $(l[ls - 5]) $(l[ls - 4]) $(l[ls - 3]) $(l[ls - 2]) $(l[ls - 1]))
      let lzip <- l[:ls - 7].foldrM (init := hd) fun s a => ``(Zippable.zip $s $a)
      let args <- i.reverse.foldl1M fun a s => ``(($s, $a))
      ``(Functor.map (fun $args => $f) $lzip)
  | `([ $f | $[$i ← $l]|* ]) => ``([ $f | $[$i <- $l]|* ])
  | `([ $f where $p | $[$i <- $l]|* ]) => do
    match h : l.size with
    | 0 => unreachable!
    | 1 => ``(                      (Functor.filterMap (fun $i* => $f depends_on! $p) $(l[0])))
    | 2 => ``(Mappable.filterMap id (Zippable.zipWith  (fun $i* => $f depends_on! $p) $(l[0]) $(l[1])))
    | 3 => ``(Mappable.filterMap id (Zippable.zipWith3 (fun $i* => $f depends_on! $p) $(l[0]) $(l[1]) $(l[2])))
    | 4 => ``(Mappable.filterMap id (Zippable.zipWith4 (fun $i* => $f depends_on! $p) $(l[0]) $(l[1]) $(l[2]) $(l[3])))
    | 5 => ``(Mappable.filterMap id (Zippable.zipWith5 (fun $i* => $f depends_on! $p) $(l[0]) $(l[1]) $(l[2]) $(l[3]) $(l[4])))
    | 6 => ``(Mappable.filterMap id (Zippable.zipWith6 (fun $i* => $f depends_on! $p) $(l[0]) $(l[1]) $(l[2]) $(l[3]) $(l[4]) $(l[5])))
    | 7 => ``(Mappable.filterMap id (Zippable.zipWith7 (fun $i* => $f depends_on! $p) $(l[0]) $(l[1]) $(l[2]) $(l[3]) $(l[4]) $(l[5]) $(l[6])))
    | _ + 8 =>
      let i := i.map fun i => ⟨i.raw.setKind `term⟩
      let ls := l.size
      let hd <- ``(Zippable.zip7 $(l[ls - 7]) $(l[ls - 6]) $(l[ls - 5]) $(l[ls - 4]) $(l[ls - 3]) $(l[ls - 2]) $(l[ls - 1]))
      let lzip <- l[:ls - 7].foldrM (init := hd) fun s a => ``(Zippable.zip $s $a)
      let args <- i.reverse.foldl1M fun a s => ``(($s, $a))
      let mf <- `(fun $args => $f depends_on! $p)
      ``(Mappable.filterMap $mf $lzip)
  | `([ $f where $p | $[$i ← $l]|* ]) => ``([ $f where $p | $[$i <- $l]|* ])

end LazyList

