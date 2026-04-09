import Lean -- for Lean.Json.escape

-- from previous chapters

inductive Pos : Type where
  | one  : Pos
  | succ : Pos → Pos

def Pos.plus : Pos → Pos → Pos
  | Pos.one, k    => Pos.succ k
  | Pos.succ n, k => Pos.succ $ n.plus k

instance : Add Pos where
  add := Pos.plus
  
def Pos.toNat : Pos → Nat
  | Pos.one    => 1
  | Pos.succ n => n.toNat + 1
  
instance : ToString Pos where
  toString x := toString $ x.toNat

def Pos.mul : Pos → Pos → Pos
  | Pos.one, k    => k
  | Pos.succ n, k => n.mul k + k

instance : Mul Pos where
  mul := Pos.mul

instance : One Pos where
  one := Pos.one

instance : OfNat Pos (n + 1) where
  ofNat := let rec natPlusOne : Nat → Pos       
             | 0     => Pos.one                 
             | k + 1 => Pos.succ $ natPlusOne k 
           natPlusOne n                         

structure NonEmptyList (α : Type) : Type where
  head : α
  tail : List α

abbrev NonEmptyList.inBounds (xs : NonEmptyList α) (i : Nat) : Prop :=
  i ≤ xs.tail.length

def NonEmptyList.get (xs : NonEmptyList α) (i : Nat) (ok : xs.inBounds i) : α :=
  match i with
  | 0     => xs.head
  | n + 1 => xs.tail[n]

instance : GetElem (NonEmptyList α) Nat α NonEmptyList.inBounds where
  getElem := NonEmptyList.get

def idahoSpiders : NonEmptyList String := {
  head := "Banded Garden Spider",
  tail := [ "Long-legged Sac Spider",
            "Wolf Spider",
            "Hobo Spider",
            "Cat-faced Spider" ]
}

/- ========= -/
/- Coercions -/
/- ========= -/

-- When Lean encounters an expression of one type in a context that expects a different type,
-- it will attempt to coerce the expression before reporting a type error.

-- The coercions are extensible by defining instances of type classes.

/- ----------------- -/
/- Strings and Paths -/
/- ----------------- -/

-- Lean defines a coercion from String to FilePath
def fileDumper : IO Unit := do
  let stdin  ← IO.getStdin
  let stdout ← IO.getStdout
  stdout.putStr "Which file? "
  stdout.flush
  let f := (← stdin.getLine).trimAscii.copy
  stdout.putStrLn s!"'The file {f}' contains:"
  stdout.putStrLn (← IO.FS.readFile f) -- automatic coercion from String to FilePath; not necessary to write IO.FS.readFile ⟨f⟩

/- ---------------- -/
/- Positive Numbers -/
/- ---------------- -/

-- List.drop expects a Nat
#eval [1, 2, 3, 4].drop (2 : Nat) 
#eval [1, 2, 3, 4].drop (2 : Pos) 

-- type class Coe describes overloaded ways of coercing from α to β another
class MyCoe (α : Type) (β : Type) where
  coe : α → β

#check Coe                        

instance : Coe Pos Nat where
  coe x := x.toNat

#eval [1, 2, 3, 4].drop (2 : Pos) 

-- Pos.toNat was used
#check [1, 2, 3, 4].drop (2 : Pos)

/- ------------------ -/
/- Chaining Coercions -/
/- ------------------ -/

-- There is already a coercion from Nat to Int.
-- Because of that instance, combined with the Coe Pos Nat instance, allows:
-- Pos -> Nat -> Int
def oneInt : Int := Pos.one

inductive A where
  | a

inductive B where
  | b

instance : Coe A B where
  coe _a := B.b

instance : Coe B A where
  coe _b := A.a

instance : Coe Unit A where
  coe __ := A.a

-- Unit -> A -> B
def coercedToB : B := ()

-- even in the presence of circular coercions the compiler finds a coercion
#eval coercedToB                

-- The Lean standard library defines a coercion from any type α to Option α that wraps the value in some. 

def List.last? : List α → Option α
  | []       => none
  | [x]      => x                    -- `some` can be omitted
  | _ :: xs  => last? xs

#eval List.last? ([] : List Nat)
#eval List.last? [1]            
#eval List.last? [1, 2]         
#eval List.last? [1, 2, 3]      

-- coercions can be chained
def perhapsPerhapsPerhaps : Option (Option (Option String)) := "Please don't tell me"

#eval perhapsPerhapsPerhaps     

-- automatic coercions not used because Lean doesn't know the type of `392`
def perhapsPerhapsPerhapsNat1 : Option (Option (Option Nat)) :=
  392                           

-- telling what type `392` is results in automatic coercion
def perhapsPerhapsPerhapsNat2 : Option (Option (Option Nat)) :=
  (392 : Nat) 

-- explicit/manual coercion (seldomly used)
def perhapsPerhapsPerhapsNat3 : Option (Option (Option Nat)) :=
  ↑(392 : Nat)

/- --------------------------------------- -/
/- Non-Empty Lists and Dependent Coercions -/
/- --------------------------------------- -/

-- allows non-empty lists to be used with the entire List API(!)
instance : Coe (NonEmptyList α) (List α) where
  coe
  | { head := x, tail := xs } => x :: xs

-- On the other hand, it is impossible to write an instance of Coe (List α) (NonEmptyList α), because there's no non-empty list that can represent the empty list.
-- This limitation can be worked around by using another version of coercions, which are called DEPENDENT COERCIONS.

-- dependent coercion takes the value being coerced as a parameter
class MyCoeDep (α : Type) (x : α) (β : Type) where
  coe : β

#check CoeDep

-- non-empty Lists can be coerced to a NonEmptyList
instance : CoeDep (List α) (x :: xs) (NonEmptyList α) where
  coe := { head := x, tail := xs }

/- ----------------- -/
/- Coercing to Types -/
/- ----------------- -/

structure Monoid where
  Carrier : Type
  neutral : Carrier
  op : Carrier → Carrier → Carrier

def natMulMonoid : Monoid :=
  { Carrier := Nat, neutral := 1, op := (· * ·) }

def natAddMonoid : Monoid :=
  { Carrier := Nat, neutral := 0, op := (· + ·) }

def stringMonoid : Monoid :=
  { Carrier := String, neutral := "", op := String.append }

def listMonoid (α : Type) : Monoid :=
  { Carrier := List α, neutral := [], op := List.append }

def foldMap1 (M : Monoid) (f : α → M.Carrier) (xs : List α) : M.Carrier :=
  let rec go (soFar : M.Carrier) : List α → M.Carrier
    | []      => soFar
    | y :: ys => go (M.op soFar $ f y) ys
  go M.neutral xs 

#eval foldMap1 natMulMonoid (· + 1) [0, 1, 2, 3, 4]               
#eval foldMap1 natMulMonoid (· + 1) [1, 2, 3, 4, 5]               
#eval foldMap1 natAddMonoid (· + 1) [1, 2, 3, 4, 5]               
#eval foldMap1 (listMonoid Nat) (fun x => [x + 1]) [1, 2, 3, 4, 5]

-- The term `sort` in Lean refers to types that classify other types.
-- The CoeSort class is just like the Coe class, with the exception that the target of the coercion must be a sort, namely Type or Prop.
-- The term sort in Lean refers to these types that classify other types.
instance : CoeSort Monoid Type where
  coe m := m.Carrier

-- with this coercion the type signatures become less bureaucratic
-- M.Carrier -> M
def foldMap (M : Monoid) (f : α → M) (xs : List α) : M :=
  let rec go (soFar : M) : List α → M
    | [] => soFar
    | y :: ys => go (M.op soFar (f y)) ys
  go M.neutral xs

-- Another useful example of CoeSort is used to bridge the gap between Bool and Prop.
-- Lean's if expression expects the condition to be a decidable proposition rather than a Bool. 

instance : Coe Bool Prop where
  coe b := Eq b true

-- CoeSort allows us to use bools in if expressions.
instance : CoeSort Bool Prop where
  coe b := b

/- --------------------- -/
/- Coercing to Functions -/
/- --------------------- -/

-- type class CoeFun can transform values from non-function types to function types
class MyCoeFun (α : Type) (makeFunctionType : outParam (α → Type)) where
  coe : (x : α) → makeFunctionType x

#check CoeFun 

-- Adder --

structure Adder where
  howMuch : Nat

def add5 : Adder := ⟨5⟩

#eval add5    

-- type Adder is not a function
#eval add5 3  

-- all Adders are transformed to Nat → Nat functions
instance : CoeFun Adder (fun _adder => Nat → Nat) where
  coe a := (· + a.howMuch)

#eval add5 3  

-- JSON --

inductive JSON where
  | true   : JSON
  | false  : JSON
  | null   : JSON
  | string : String → JSON
  | number : Float → JSON
  | object : List (String × JSON) → JSON
  | array  : List JSON → JSON

-- a JSON serializer is a structure that tracks the type it knows how to serialize along with the serialization code itself
structure JSONSerializer where
  Contents  : Type
  serialize : Contents → JSON

-- string serializer
def StrSerializer : JSONSerializer :=
  { Contents  := String,
    serialize := JSON.string
  }

-- JSON serializer as a function
instance : CoeFun JSONSerializer (fun serializer => serializer.Contents → JSON) where
  coe s := s.serialize

def buildResponse (title : String) (R : JSONSerializer) (record : R.Contents) : JSON :=
  JSON.object [ ("title",  JSON.string title),
                ("status", JSON.number 200),
                ("record", R record)] -- a serializer can now be applied directly to an argument

#eval buildResponse "Functional Programming in Lean" StrSerializer "Programming is fun!"

/- ----------------------- -/
/- Aside: JSON as a String -/
/- ----------------------- -/

-- JSON doesn't distinguish between integers and floating point numbers, and the type Float is used to represent both.

-- but Lean generates trailing zeros
#eval (5 : Float).toString                   

def dropDecimals (numString : String) : String :=
  if numString.contains '.' then
    let noTrailingZeros := numString.dropEndWhile (· == '0')
    (noTrailingZeros.dropEndWhile (· == '.')).copy
  else numString

#eval dropDecimals (5   : Float).toString    
#eval dropDecimals (5.2 : Float).toString    

def String.separate (sep : String) (strings : List String) : String :=
  match strings with
  | []      => ""
  | x :: xs => String.join $ x :: xs.map (sep ++ ·)

#eval String.separate    ", " ["a", "b", "c"]
#eval String.intercalate ", " ["a", "b", "c"]

#eval ", ".separate []                       
#eval ", ".separate ["1"]                    
#eval ", ".separate ["1", "2"   ]            

#eval ", ".intercalate []                    
#eval ", ".intercalate ["1"]                 
#eval ", ".intercalate ["1", "2"            ]

-- `partial` because Lean cannot see that it terminates
partial def JSON.asString (val : JSON) : String :=
  match val with
  | true           => "true"
  | false          => "false"
  | null           => "null"
  | string s       => "\"" ++ Lean.Json.escape s ++ "\""
  | number n       => dropDecimals n.toString
  | array elements => "[" ++ ", ".separate (elements.map asString) ++ "]"
  | object members => let memberToString mem := "\"" ++ Lean.Json.escape mem.fst ++ "\": " ++ asString mem.snd
                      "{" ++ ", ".separate (members.map memberToString) ++ "}"

-- don't know what the effect of `escape` should really be
#eval Lean.Json.escape "Hello!"

#eval (buildResponse "Functional Programming in Lean" StrSerializer "Programming is fun!").asString

/- --------------------- -/
/- Messages You May Meet -/
/- --------------------- -/

-- Natural number literals are overloaded with the OfNat type class.
-- Because coercions fire in cases where types don't match, rather
-- than in cases of missing instances, a missing OfNat instance for
-- a type does not cause a coercion from Nat to be applied.

def perhapsPerhapsPerhapsNat : Option (Option (Option Nat)) := 392

/- --------------------- -/
/- Design Considerations -/
/- --------------------- -/

-- When a coercion is not applied for some reason, the user receives the original type error,
-- which can make it difficult to debug chains of coercions.

-- works because of the automatic coercion from non-empty lists to lists
-- but needs type annotations
def lastSpider1 : Option String :=
  List.getLast? idahoSpiders

-- without type annotations we get an error
def lastSpider2 :=
  List.getLast? idahoSpiders

-- Note: coercions are not applied in the context of field accessor notation.
