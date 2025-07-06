import Lean

-- set_option diagnostics true
set_option diagnostics false

class Plus (α : Type) where
  plus : α -> α -> α

instance : Plus Nat where
  plus := Nat.add

open Plus (plus)

#eval plus 34 35

inductive Pos : Type where
  | one : Pos
  | suc : Pos -> Pos

def Pos.plus : Pos -> Pos -> Pos
| .one,   k => .suc k
| .suc n, k => n.plus k.suc

def Pos.toString (top : Bool) (p : Pos) : String :=
  let paren s := if top then s else "(" ++ s ++ ")"
  match p with
  | .one   => "Pos.1"
  | .suc n => paren s!"Pos.suc {n.toString false}"

def Pos.toNat : Pos -> Nat
  | .one   => 1
  | .suc n => n.toNat + 1

instance : Plus Pos where
  plus := .plus

instance : Add Pos where
  add := .plus

def Pos.mult : Pos -> Pos -> Pos
| .one,   k => k
| .suc n, k => n.mult k + k

instance : Mul Pos where
  mul := .mult

instance : ToString Pos where
  toString x := toString x.toNat

#eval Plus.plus .one Pos.one.suc.suc

def seven : Pos := Pos.one.suc.suc.suc.suc.suc.suc

#eval plus seven seven
#eval seven + seven

#eval s!"There are {seven} things"

#eval seven * seven

#eval [seven, .one, Pos.one.suc.suc.suc].map (· + .one)

instance : OfNat Pos (n + 1) where
  ofNat :=
    let rec natPlusOne : Nat -> Pos
        | 0     => .one
        | n + 1 => (natPlusOne n).suc
    natPlusOne n

#eval (1 : Pos).suc.suc

structure Poss where
  succ::
    pred : Nat

#eval Poss.succ 4

def Poss.add : Poss -> Poss -> Poss
  | { pred := a }, { pred := b } =>
    succ (a + b + 1)

instance : Add Poss where
  add := .add

def Poss.mul : Poss -> Poss -> Poss
 | { pred := 0 }, b => b
 | { pred := n + 1 }, b => b + (succ n).mul  b

instance : Mul Poss where
  mul := .mul

instance : ToString Poss where
  toString x := match x with
    | { pred := n } => toString (n + 1)

instance : OfNat Poss (n + 1) where
  ofNat := .succ n

def five := Poss.succ 4

#eval five + five
#eval five * five

#eval (28 : Poss).add (five.mul 7)

-- def evenn (n : Int) (IsEven n) : Even

def Nat.isEven : Nat -> Bool
| 0     => true
| n + 1 => !n.isEven

def Int.isEven : Int -> Bool
  | 0          => true
  | .ofNat n   => !n.isEven
  | .negSucc n => !n.isEven

#eval Nat.isEven 15

#eval (Int.negSucc 10).isEven
#eval Int.negSucc 0
#eval Int.ofNat 3

abbrev IsEven n := Int.isEven n = true

structure Even where
  evenn::
    n : Prop

inductive EvenNat : Nat -> Type where
  | zero     : EvenNat .zero
  | succEven : {n : Nat} -> EvenNat n -> EvenNat n.succ.succ

def four_is_even : EvenNat 4 := EvenNat.zero.succEven.succEven

def EvenInt := { x : Int // x % 2 == 0 }

instance : Add EvenInt where
  add a b := ⟨a.val + b.val, by
    apply Int.emod_eq_zero_of_dvd
    have ha : 2 ∣ a.val := Int.dvd_of_emod_eq_zero a.property
    have hb : 2 ∣ b.val := Int.dvd_of_emod_eq_zero b.property
    exact dvd_add ha hb
  ⟩

instance : Mul EvenInt where
  mul a b := ⟨a.val * b.val, by
    apply Int.emod_eq_zero_of_dvd
    have ha : 2 ∣ a.val := Int.dvd_of_mod_eq_zero a.property
    exact dvd_mul_of_dvd_left ha b.val
  ⟩

instance : ToString EvenInt where
  toString a := toString a.val

instance : Coe EvenInt Int where
  coe a := a.val

inductive HTTPMethod where
| get    : HTTPMethod
| put    : HTTPMethod
| update : HTTPMethod
| delete : HTTPMethod

instance : ToString HTTPMethod where
  toString : HTTPMethod -> String
  | .get    => "GET"
  | .put    => "PUT"
  | .update => "UPDATE"
  | .delete => "DELETE"

structure HTTPRequest where
  req::
    method : HTTPMethod
    uri     : String
    vesrion : String

instance : ToString HTTPRequest where
  toString : HTTPRequest -> String
  | { method, uri, vesrion } =>
  s!"HTTP Request
  method  = {method}
  URI     = {uri}
  Version = {vesrion}"

def areq : HTTPRequest :=
  .req .get "/users" "HTTP/1.0"

def breq : HTTPRequest :=
  { method := .put
  , uri := "/user"
  , vesrion := "HTTP/2.0"
  }

#eval areq
#eval breq

structure HTTPResponse where
  resp::
    code    : Nat
    version : String
    message : String

instance : ToString HTTPResponse where
  toString : HTTPResponse -> String
  | { code, version, message } =>
  s!"HTTP Response
  Status Code = {code}
  Version     = {version}
  Message     = {message}"


def aresp : HTTPResponse :=
  .resp 200 "HTTP/2.0" "OK"

#eval aresp


def HTTPMethod.toIO : HTTPMethod -> String -> IO HTTPResponse
| method, uri => pure (.resp 200 "HTTP/1.0" s!"{method}'ed {uri}")

def HTTPMethod.getIO (_uri : String) : IO HTTPResponse
  := do
    pure (.resp 200 "HTTP/2.0" s!"list of users")

#eval HTTPMethod.update.toIO "/users"

#check IO.println

def List.jumlah [Add α] [Zero α] : List α -> α
| [] => 0
| x :: xs => x + xs.jumlah

#check Add.add

#eval [1, 2, 3, 4].jumlah
-- [1, 2, 3, 4].jumlah
-- 1 + [2, 3, 4].jumlah
-- 1 + 2 + [3, 4].jumlah
-- 1 + 2 + 3 + [4].jumlah
-- 1 + 2 + 3 + 4 + [].jumlah
-- 1 + 2 + 3 + 4 + 0
-- 10

structure PPoint (α : Type) where
  x : α
  y : α

instance [Add α] : Add (PPoint α) where
  add a b :=
    { x := a.x + b.x
    , y := a.y + b.y
    }

#check OfNat.ofNat

def addPosNat : Pos -> Nat -> Pos
| p, 0     => p
| p, n + 1 => .suc (addPosNat p n)

def addNatPos : Nat -> Pos -> Pos
| 0,     p => p
| n + 1, p => .suc (addNatPos n p)

instance : HAdd Pos Nat Pos where
  hAdd := addPosNat

instance : HAdd Nat Pos Pos where
  hAdd := addNatPos

#eval (34 : Pos) + (35 : Nat)

class HPlus (α : Type) (β : Type) (γ : outParam Type) where
  hPlus : α -> β -> γ

instance : HPlus Pos Nat Pos where
  hPlus := addPosNat

instance : HPlus Nat Pos Pos where
  hPlus := addNatPos

#eval HPlus.hPlus (34 : Pos) (35 : Nat)

@[default_instance]
instance [Add α] : HPlus α α α where
  hPlus := Add.add

def add3 (n : Nat) : Nat := HPlus.hPlus 3 n

#check (HPlus.hPlus 3)

instance [Mul α] : HMul (PPoint α) α (PPoint α) where
  hMul p s := { x := p.x * s , y := p.y * s }

#eval { x := 1.2 , y := 3 : PPoint Float} * 2.

#eval #["sloe", "birch", "elm"][1]

structure NonEmptyList (α : Type) where
  head : α
  tail : List α

infix : 90 "@@" => NonEmptyList.mk
infixl : 70 "mix" => mixHash


#eval 1 @@ [2,3]

def NonEmptyList.get? : NonEmptyList α -> Nat -> Option α
| xs, 0     => xs.head
| xs, n + 1 => xs.tail[n]?

def lis : NonEmptyList Nat := 1 @@ [1,1,2,2,3,3,4,5]

#eval lis
#eval lis.get? 3

abbrev NonEmptyList.inbounds
    (xs : NonEmptyList α)
    (i  : Nat)
    :  Prop
    := i ≤ xs.tail.length

theorem atleatsthreenumber : lis.inbounds 3 := by decide
theorem notmorethan100number : ¬ lis.inbounds 100 := by decide

def NonEmptyList.get
    (xs : NonEmptyList α)
    (ix : Nat)
    (ok : xs.inbounds ix)
    : α :=
        match ix with
        | 0 => xs.head
        | n + 1 => xs.tail[n]

def something := lis.get 3 (by decide)
#eval something

instance :
    GetElem (NonEmptyList α) Nat α NonEmptyList.inbounds
  where
    getElem := NonEmptyList.get

#eval lis[8]

#eval 2 < 4
#check if 2 < 3 then 1 else -1

instance : LT Pos where
    lt x y := LT.lt x.toNat y.toNat

instance : LE Pos where
    le x y := LE.le x.toNat y.toNat

def twelve : Pos := 12
def forty  : Pos := 40

instance {x y : Pos } : Decidable (x < y) :=
    inferInstanceAs (Decidable (x.toNat < y.toNat))

instance {x y : Pos } : Decidable (x <= y) :=
    inferInstanceAs (Decidable (x.toNat <= y.toNat))

#check twelve < forty
#eval twelve >= forty

def Pos.comp : Pos -> Pos -> Ordering
    | .one, .one => .eq
    | .one, .suc _ => .lt
    | .suc _, .one => .gt
    | .suc a, .suc b => Pos.comp a b

instance : Ord Pos where
    compare := Pos.comp

def Pos.hash : Pos -> UInt64
    | .one => 0
    | .suc n => 1 mix n.hash

instance : Hashable Pos where
    hash := Pos.hash

instance [Hashable α] : Hashable (NonEmptyList α) where
    hash xs := hash xs.head mix hash xs.tail

inductive Tree (α : Type) where
    | leaf : Tree α
    | branch : Tree α -> α -> Tree α -> Tree α

def Tree.beq [BEq α] : Tree α -> Tree α -> Bool
    | .leaf, .leaf => true
    | .branch l1 a1 r1, .branch l2 a2 r2 =>
        a1 == a2 && l1.beq l2 && r1.beq r2
    | _, _ => false

instance : BEq Pos where
    beq a b := a.toNat == b.toNat

instance [BEq α] : BEq (Tree α) where
    beq := Tree.beq

def Tree.toString [ToString α] : Tree α -> String
    | .leaf => "🌿"
    | .branch l a r =>
        s!"🪵({l.toString} [{a}] {r.toString})"

instance [ToString α] : ToString (Tree α) where
    toString := Tree.toString

def Tree.hash [Hashable α] : Tree α -> UInt64
    | .leaf => 0
    | .branch l a r =>
        1 mix l.hash mix Hashable.hash a mix r.hash

instance [Hashable α] : Hashable (Tree α) where
    hash := Tree.hash

def atree : Tree Pos :=
    .branch .leaf 6 (.branch .leaf 9 .leaf)

-- deriving instance Repr, Hashable, Ord, BEq for Pos
deriving instance Repr, Hashable, Ord, BEq for Tree

#eval atree

#eval atree == (Tree.branch .leaf 6 (.branch .leaf 9 .leaf))
#eval atree.hash == (Tree.branch .leaf (6 : Pos) (.branch .leaf 9 .leaf)).hash

def pepe := "pepe"
#eval hash pepe
#eval hash "pepe"

instance : Append (NonEmptyList α) where
    append xs ys :=
        xs.head @@ (xs.tail ++ ys.head :: ys.tail)

def newlis := { lis with head := 12 }

#eval lis ++ newlis

instance : Functor NonEmptyList where
    map f xs :=
        { head := f xs.head, tail := f <$> xs.tail }

def NonEmptyList.map
    (f  : α -> β)
    (xs : NonEmptyList α)
    :  NonEmptyList β
    := Functor.map f xs

#eval lis.map (· + 10)

instance : HAppend (List α) (NonEmptyList α) (NonEmptyList α)
  where
    hAppend : List α -> NonEmptyList α -> NonEmptyList α
    | [], ne => ne
    | h :: t, .mk h' t' =>
        { head := h, tail := t ++ (h' :: t') }

#eval [1,2,3,4,5] ++ (12 @@ [4,3,2,1])

def Tree.map : (α -> β) -> Tree α -> Tree β
| _, .leaf         => .leaf
| f, .branch l a r => .branch (l.map f) (f a) (r.map f)

instance : Functor Tree where
    map := Tree.map

#eval toString <$> (· + 10) <$> atree

instance : Coe Pos Nat where
    coe := Pos.toNat

#eval  [1,2,3,4,5,6,7,8,9,1,2,3,4,5,6,7,8,9].drop seven
#check [1,2,3,4,5,6,7,8,9,1,2,3,4,5,6,7,8,9].drop (2 : Pos)

#check ↑12

def NonEmptyList.toList : NonEmptyList α -> List α
    | .mk h t => h :: t

instance : Coe (NonEmptyList α) (List α) where
    coe := NonEmptyList.toList

def the_two : List Nat := List.drop 7 lis
def len : Nat := List.length lis.toList
#eval the_two

instance : CoeDep Nat (n + 1) Pos where
    coe :=
        let rec natPlusOne : Nat -> Pos
            | 0     => .one
            | n + 1 => (natPlusOne n).suc
        natPlusOne n

def NonEmptyList.length : NonEmptyList α -> Pos
    | .mk _ t => t.length + 1

#eval lis.length

/- Monoid -/

structure Monoid where
    Carrier : Type
    neutral : Carrier
    op      : Carrier -> Carrier -> Carrier

instance : CoeSort Monoid Type where
    coe m := m.Carrier

infix : 60 "<>" => Monoid.op

def natMulMonoid : Monoid :=
    { Carrier := Nat
    , op      := (·*·)
    , neutral := 1
    }

def Monoid.foldMap
    (M  : Monoid)
    (f  : α -> M)
    (xs : List α)
    : M :=
    let rec go (so_far : M) : List α -> M
        | []     => so_far
        | h :: t => go (M.op so_far (f h)) t
    go M.neutral xs

structure Adder where
    howMuch : Nat

instance : CoeFun Adder (fun _ => Nat -> Nat) where
    coe a := (·+ a.howMuch)

def add_5 : Adder := ⟨5⟩

#eval add_5 (8*8)

inductive JSON where
    | true   : JSON
    | false  : JSON
    | null   : JSON
    | string : String -> JSON
    | number : Float -> JSON
    | object : List (String × JSON) -> JSON
    | array  : List JSON -> JSON
deriving Repr

structure Serializer where
    Content   : Type
    serialize : Content -> JSON

def Str : Serializer := ⟨String, JSON.string⟩
def Flt : Serializer := ⟨Float, JSON.number⟩

instance : CoeFun Serializer (fun s => s.Content -> JSON)
  where
    coe s := s.serialize

instance : CoeSort Serializer Type where
    coe s := s.Content

def buildResponse
    (title  : String)
    (R      : Serializer)
    (record : R)
    : JSON :=
    JSON.object
        [ ("title",  JSON.string title)
        , ("status", JSON.number 200)
        , ("record", R record)
        ]

#eval (buildResponse "user" Str "LitFill")

#eval (JSON.string "LitFill")

def dropDecimals (numStr : String) : String :=
    if numStr.contains '.' then
        let noTrailZero := numStr.dropRightWhile (·== '0')
        noTrailZero.dropRightWhile (·== '.')
    else numStr

def Float.toStringCompact := dropDecimals ∘ toString

#eval dropDecimals (2.3000000).toString
#eval 02.92040.toStringCompact
#eval (6 : Float).toStringCompact

#eval (toString <$> List.range 10)
#eval ", ".intercalate (toString <$> List.range 10)
#eval ", ".intercalate ["1"]

def String.surround (str lf rg : String) : String :=
    lf ++ str ++ rg

def String.paren (str : String) (lf := "(") (rg := ")") :=
    str.surround lf rg

#eval (", ".intercalate (toString <$> List.range 10)).surround "[" "]"
#eval (", ".intercalate (toString <$> List.range 10)).paren "[" "]"

#eval Lean.Json.escape "Hello!"

partial
def JSON.toString : JSON -> String
| .null => "null"
| .true => "true"
| .false => "false"
| .string s => s!"\"{Lean.Json.escape s}\""
| .number n => n.toStringCompact
| .object mems =>
    let memToSring mem := s!"\"{Lean.Json.escape mem.fst}\": {mem.snd.toString}"
    (", ".intercalate (mems.map memToSring)).paren "{" "}"
| .array els =>
    (", ".intercalate (els.map toString)).paren "[" "]"

instance : ToString JSON where
    toString := JSON.toString

instance : ToString JSON :=
    { toString := JSON.toString }

instance : ToString JSON := ⟨JSON.toString⟩

def litfillUser := buildResponse "USER" Str "LitFill"
def weight := buildResponse "weight" Flt (50.3 : Float)

#eval toString weight

def test : IO Unit := do
    (<- IO.getStdout).putStrLn litfillUser.toString

#eval test
