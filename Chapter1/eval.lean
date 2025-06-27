#eval 34 + 5 * 7

def hello := "Hello, "
#eval String.append hello "Lean!"

#eval if 3 == 4 then 5 else 7
#eval 3 == 4
#check Nat.add

#eval (1 - 2 : Int)
#eval ([] : List Bool)

def add1 (n : Nat) : Nat := n + 1
def Float.add1 (f : Float) : Float := f + 1

def appendwithspace (a b : String) : String
  := a ++ " " ++ b

#eval appendwithspace "Hello" "World"

def joinStringWith (joiner a b : String) : String
  := a ++ joiner ++ b

#eval joinStringWith ", " "Hello" "World"

def volume (x y z : Float) : Float
  := x * y * z

abbrev N := Nat

def a : N := 69

#check 0.

structure Point where
  point ::
    x : Float
    y : Float
deriving Repr

def origin : Point :=
  { x := 0.
  , y := 0.
  }

#eval origin
#eval origin.x
#check origin

def addPoint (a b : Point) : Point
  := { x := a.x + b.x
     , y := a.y + b.y }

def other := addPoint origin { x := -12, y := 12}

def pointDistance (a b : Point) : Float
  := Float.sqrt (((b.x - a.x) ^ 2.) + ((b.y - a.y) ^ 2.))

#eval pointDistance origin other

def zeroedX (p : Point) : Point
  := { p with x := 0 }

#eval zeroedX other

#check Point.point 12 13
#check Point.x

def Point.modifyXY (f : Float → Float) (p : Point) : Point
  := { x := f p.x, y := f p.y }

#eval origin.modifyXY Float.add1

structure RectangularPrism where
  width  : Float
  height : Float
  depth  : Float
deriving Repr

def RectangularPrism.volume (p : RectangularPrism) : Float
  := p.width * p.height * p.depth

def cube : RectangularPrism :=
  { width := 2.
  , height := 2.
  , depth := 2. }

#eval cube.volume

structure Segment where
  a : Point
  b : Point
deriving Repr

def Segment.length (s : Segment) : Float
  := pointDistance s.a s.b

#eval Segment.length
  (Segment.mk (Point.point 0 4) (Point.point 3 0))

inductive Natural where
  | zero               : Natural
  | succ (n : Natural) : Natural
deriving Repr

def Natural.isZero (n : Natural) : Bool
  := match n with
    | zero   => true
    | succ _ => false

def Natural.pred (n : Natural) : Natural
  := match n with
    | zero   => zero
    | succ k => k

def Natural.even (n : Natural) : Bool
  := match n with
    | zero   => true
    | succ k => not (even k)

def Natural.add (a b : Natural) : Natural
  := match b with
    | zero => a
    | succ n => succ (add a n)

def Natural.times (a b : Natural) : Natural
  := match b with
    | zero => zero
    | succ n => add a (times a n)

def Natural.minus (a b : Natural) : Natural
  := match b with
    | zero => a
    | succ n => pred (minus a n)

structure PPoint (α : Type) where
  x : α
  y : α
deriving Repr

def Natural.origin : PPoint Natural
  := { x := zero, y := zero }

def replaceX {α : Type} (p : PPoint α) (newX : α) : PPoint α
  := { p with x := newX }

#check (replaceX)
#eval replaceX
  Natural.origin (Natural.succ (Natural.succ Natural.zero))
#eval replaceX { x := 0, y := 0 } 12

inductive Sign where
  | pos : Sign
  | neg : Sign

def posOrNegThree (s : Sign)
  :  match s with
    | .pos => Nat
    | .neg => Int
  := match s with
    | .pos =>  3
    | .neg => -3

def length {α : Type} (l : List α) : Natural
  := match l with
    | []      => .zero
    | _ :: xs => .succ (length xs)

#check (List.length (α := Int))

-- Exercise 1.6.5

def last : List α → Option α
  | []      => none
  | [x]     => some x
  | _ :: xs => last xs

#eval last [1, 2, 3]
#eval last [] (α := Int)

def List.findFirst?
  (l : List α) (p : α → Bool)
  :  Option α
  := match l with
    | []      => none
    | x :: xs =>
      match p x with
        | false => findFirst? xs p
        | true  => some x

-- this one better
def List.findFirst'? (p : α → Bool) : List α → Option α
  | []      => none
  | x :: xs =>
    match p x with
      | true  => some x
      | false => findFirst'? p xs

def Nat.even : Nat → Bool
  | 0     => true
  | n + 1 => not (even n)

#eval [1,3,5,4,7,9,0].findFirst? Nat.even

def Prod.switch :  α × β → β × α
  | (a, b) => (b, a)

#eval (69, true).switch

def List.myzip : List α → List β → List (α × β)
  | []     , _       => []
  | _      , []      => []
  | x :: xs, y :: ys => (x , y) :: myzip xs ys

def List.mytake : Nat → List α → List α
  | 0    , _       => []
  | _    , []      => []
  | n + 1, x :: xs => x :: mytake n xs

#eval [1,2,3].mytake 10
#eval [1,2,3].mytake 2
#eval [1,2,3].mytake 1
#eval [1,2,3].mytake 0

def distProdSum : α × (β ⊕ γ) →  (α × β) ⊕ (α × γ)
  | (a, x) =>
    match x with
      | .inl b => .inl (a, b)
      | .inr c => .inr (a, c)

def boolαSum : Bool × α → α ⊕ α
  | (true,  a) => .inl a
  | (false, a) => .inr a

def List.myunzip : List (α × β) → List α × List β
  | [] => ([],[])
  | (x, y) :: xys =>
    let (xs, ys) := xys.myunzip
    (x :: xs, y :: ys)

def add1' := (· + 1)
#check add1'

def origin' : Point := ⟨0, 0⟩
