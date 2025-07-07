def andThen (opt : Option α) (next : α -> Option β) : Option β :=
    match opt with
    | .none => .none
    | .some a => next a

def firstandthird (xs : List α) : Option (α × α) :=
    andThen xs[0]? fun first =>
    andThen xs[2]? fun third =>
    (first, third)

#eval firstandthird [2,3,4,5]

infixl : 65 " ~~> " => andThen

def firstandthird' (xs : List α) : Option (α × α) :=
    xs[0]? ~~> fun first =>
    xs[2]? ~~> fun third =>
    (first, third)

inductive MyExcept (ε α : Type) where
    | err : ε -> MyExcept ε α
    | ok  : α -> MyExcept ε α
deriving BEq, Hashable, Repr

def get (xs : List α) (i : Nat) : MyExcept String α :=
    match xs[i]? with
    | none   => .err s!"index {i} is not found, maximum is {xs.length - 1}."
    | some x => .ok  x

#eval get [1,2,3,4] 5

def Int.isEven (x : Int) := x % 2 == 0

def sumAndFindEven : List Int -> List Int × Int
| [] => ([], 0)
| x :: xs =>
    let (more, sum) := sumAndFindEven xs
    ( if x.isEven then x :: more else more
    , sum + x)

#eval sumAndFindEven [1, 2, 3, 4, 5, 6, 7, 8, 9]

inductive Tree α where
    | leaf   : Tree α
    | branch : Tree α -> α -> Tree α -> Tree α

def Tree.beq [BEq α] : Tree α -> Tree α -> Bool
    | .leaf, .leaf => true
    | .branch l1 a1 r1, .branch l2 a2 r2 =>
        a1 == a2 && l1.beq l2 && r1.beq r2
    | _, _ => false

instance [BEq α] : BEq (Tree α) where
    beq := Tree.beq

def Tree.toString [ToString α] : Tree α -> String
    | .leaf => "🌿"
    | .branch l a r =>
        s!"🪵({l.toString} [{a}] {r.toString})"

instance [ToString α] :
    ToString (Tree α) := ⟨Tree.toString⟩

def Tree.insert [Ord α] : α -> Tree α -> Tree α
    | x, .leaf => .branch .leaf x .leaf
    | x, .branch lf a rg =>
        match compare x a with
        | .gt => .branch  lf           a (rg.insert x)
        | .lt => .branch (lf.insert x) a  rg
        | .eq => .branch  lf           a  rg

#eval [1, 2, 3].foldl (flip Tree.insert) .leaf

def Tree.fromList [Ord α] (ls : List α) : Tree α :=
    ls.foldl (flip Tree.insert) .leaf

def List.toTree [Ord α] (ls : List α) : Tree α :=
    Tree.fromList ls

-- def List.toTree [Ord α] : List α -> Tree α
--     | ls => Tree.fromList ls

#eval ["vedal", "neuro", "evil"].toTree

def Tree.inordersum : Tree Int -> List Int × Int
    | .leaf => ([], 0)
    | .branch l a r =>
        let (l'ed, lsum) := l.inordersum
        let (a'ed, asum) := ([a], a)
        let (r'ed, rsum) := r.inordersum
        ( l'ed ++ a'ed ++ r'ed
        , lsum + asum + rsum)

#eval [1,2,7,3,4,6,5,8,9].toTree.inordersum

structure WithLog (logged : Type) (μ : Type) where
    log : List logged
    val : μ

def WithLog.andThen
    (result : WithLog μ α)
    (next   : α -> WithLog μ β)
    : WithLog μ β :=
        let ⟨thisOut, thisRes⟩ := result
        let ⟨nextOut, nextRes⟩ := next thisRes
        ⟨thisOut ++ nextOut, nextRes⟩

def WithLog.pure (x : α) : WithLog μ α := ⟨[], x⟩
def WithLog.save (data : μ) : WithLog μ Unit := ⟨[data], ()⟩

infixl : 55 " ~~> " => WithLog.andThen

def sumAndFindEven' : List Int -> WithLog Int Int
| [] => .pure 0
| x :: xs =>
    open WithLog in
    (if x.isEven then save x else pure ()) ~~> fun () =>
    sumAndFindEven' xs ~~> fun sum =>
    pure (x + sum)

open Tree in
def Tree.inordersum' : Tree Int -> WithLog Int Int
    | leaf => .pure 0
    | branch l a r =>
        open WithLog in
        l.inordersum' ~~> fun lsum =>
        save a        ~~> fun ()   =>
        r.inordersum' ~~> fun rsum =>
        pure (lsum + a + rsum)

open Tree in
def aTree :=
  branch
    (branch
       (branch leaf "a" (branch leaf "b" leaf))
       "c"
       leaf)
    "d"
    (branch leaf "e" leaf)

#eval aTree

def Tree.numbering (t : Tree α) : Tree (Nat × α) :=
    let rec aux (n : Nat) : Tree α -> (Nat × Tree (Nat × α))
        | .leaf => (n, .leaf)
        | .branch l a r =>
            let (k, num'dLeft) := aux n l
            let (i, num'dRight) := aux (k + 1) r
            (i, .branch num'dLeft (k, a) num'dRight)
    (aux 0 t).snd

#eval aTree.numbering

/- it's like Haskell's
type State s a = s -> (s, a)
-/
def State (σ : Type) (α : Type) : Type
    := σ -> (σ × α)

#check State

def State.ok (x : α) : State σ α :=
    λ s => (s, x)

def State.get : State σ σ :=
    fun s => (s, s)

def State.set (s : σ) : State σ Unit :=
    fun _ => (s, ())

def State.andThen
    (first : State σ α)
    (next  : α -> State σ β)
    : State σ β :=
        fun s =>
            let (s', x) := first s
            next x s'

infixl : 55 " ~~> " => State.andThen

def Tree.numbering' (t : Tree α) : Tree (Nat × α) :=
    let rec aux : Tree α -> State Nat (Tree (Nat × α))
        | leaf => .ok leaf
        | branch l a r =>
            aux l        ~~> λ num'dLeft =>
            .get         ~~> λ n =>
            .set (n + 1) ~~> λ () =>
            aux r        ~~> λ num'dRight =>
            .ok (branch num'dLeft (n, a) num'dRight)
    (aux t 0).snd

/- I call these >>=λ(x)=> monad arrows -/

def LitFill.mapM [Monad m]
    (f : α -> m β)
    : List α -> m (List β)
    | []      => pure []
    | x :: xs =>
        f x >>=λ(x')=>
        mapM f xs >>=λ(xs')=>
        pure (x' :: xs')

def LitFill.mapM' [Monad m]
    (f : α -> m β)
    : List α -> m (List β)
    | []      => pure []
    | x :: xs => do
        let x'  <- f x
        let xs' <- LitFill.mapM' f xs
        pure (x' :: xs')

class LitFill.Monad (m : Type -> Type) where
    pure : α -> m α
    bind : m α -> (α -> m β) -> m β

instance : Monad (State σ) where
    pure a    := λ s => (s, a)
    bind ma f := λ s =>
        let (s', a) := ma s
        f a s'

def State.increment (howMuch : Int) : State Int Int :=
    get >>=λ(i)=> set (i + howMuch) >>=λ()=> pure i

def State.increment' (howMuch : Int) : State Int Int := do
    let i <- get
    set (i + howMuch)
    pure i

#eval [1, 2, 3, 4, 5].mapM State.increment 0
#check [1, 2, 3, 4, 5].mapM State.increment

instance : Monad (WithLog μ) where
    pure a := ⟨[], a⟩
    bind ma f :=
        let ⟨log, val⟩ := ma
        let ⟨log', val'⟩ := f val
        ⟨log ++ log', val'⟩

/- it is like filter in the .log -/
def safeIsEven (i : Int) : WithLog Int Int :=
    ( if i.isEven
        then .save i
        else pure ()
    ) >>=λ()=> pure i

#eval [1, 2, 3, 4, 5, 6].mapM safeIsEven
#eval ([1, 2, 3, 4, 5, 6].mapM safeIsEven).log

def Tree.mapM [Monad m] (f : α -> m β) : Tree α -> m (Tree β)
    | leaf => pure leaf
    | branch l a r => do
        let lm <- l.mapM f
        let am <- f a
        let rm <- r.mapM f
        pure (branch lm am rm)
