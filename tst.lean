#eval 1 + 3 * 5

#eval String.append "Hello, " "Lean!"

#eval String.append "great " (String.append "oak " "tree")

#eval String.append "it is " (if 1 > 2 then "yes" else "no")

#eval 42 + 19

#eval String.append "A" (String.append "B" "C")

#eval String.append (String.append "A" "B") "C"

#eval if 3 == 3 then 5 else 7

#eval if 3 ==4 then "equal" else "not equal"

#eval (1 + 2 : Nat)

#eval 1 - 2

#eval (1 - 2 : Nat)

#eval (1 - 2 : Int)

#check (1 - 2 : Int)

#check (1 - 2)

/- #check String.append ["hello", " "] "world" -/

def hello := "Hello"

def lean : String := "Lean"

#eval String.append " " lean

#eval String.append hello (String.append " " lean)

def add1_1 n := n + 1

#eval add1_1 5

def add1_2 (n : Nat) : Nat := n + 1

#eval add1_2 5

/- def maximum1 n k : Nat := -/
/-   if n < k then -/
/-     k -/
/-   else n -/
  
def maximum2 (n : Nat) (k : Nat) : Nat :=
  if n < k then
    k
  else n 

#eval maximum2 2 5

def spaceBetween1 (before : String) (after : String) : String :=
  String.append before (String.append " " after)
  
/- def spaceBetween2 before after : String := -/
/-   String.append before (String.append " " after) -/

#check  spaceBetween1
#check (spaceBetween1)

/- Define the function joinStringsWith with type String → String → String → String that creates a new string by placing its first argument between its second and third arguments. joinStringsWith ", " "one" "and another" should evaluate to "one, and another". -/

def joinStringsWith sep before after := String.append before (String.append sep after)

#check joinStringsWith

#eval joinStringsWith ", " "one" "and another"

#check joinStringsWith ": "

def volume (height : Nat) width depth := height * width * depth

#check volume
#check (volume)

/- def Str : Type := String -/

def Str := String
/- abbrev Str := String -/

def aStr : Str    := "This is a string."
def bStr : String := "This is another string."

#eval aStr ++ aStr
#eval bStr ++ bStr

/- def NaturalNumber : Type := Nat -/
def NaturalNumber := Nat

/- def thirtyEight : NaturalNumber := 38 -/

def thirtyEight : NaturalNumber := (38 : Nat)

abbrev N := Nat

def thirtyNine : N := 39

#check 1.2
#check -454.2123215
#check 0.0

#check 0
#check (0 : Float)

structure Point where
  x : Float
  y : Float

def origin : Point := { x := 0.0,
                        y := 0.0 }

#eval origin                       

#eval origin.x
#eval origin.y

def addPoints (p1 : Point) (p2 : Point) : Point :=
  { x := p1.x + p2.x,
    y := p1.y + p2.y }

def p1 : Point := { x := 1.5, y := 32 }
def p2 : Point := { x := -8,  y := 0.2 }
  
#eval addPoints p1 p2 

def distance (p1 : Point) (p2 : Point) : Float :=
  Float.sqrt (((p2.x - p1.x) ^ 2.0) + ((p2.y - p1.y) ^ 2.0))

#eval distance p1 p2

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0,
                            y := 0.0,
                            z := 0.0 }

#check ({ x := 0.0, y := 0.0 } : Point)
#check { x := 0.0, y := 0.0 : Point}

/- def zeroX (p : Point) : Point := { x := 0, -/
/-                                    y := p.y } -/

def zeroX (p : Point) : Point := { p with x := 0 }

def fourAndThree : Point := { x := 4.3, y := 3.4 }

#eval fourAndThree
#eval zeroX fourAndThree
#eval fourAndThree

#check Point.mk 1.5 2.8

#check (Point.mk)
#check (Point.x)
#check (Point.y)

#eval origin.x
#eval Point.x origin

structure MyPoint where
  point :: /- new constructor name -/
  x : Float
  y : Float

#check MyPoint.point 1.5 2.8

#eval "one string".append " and another"

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

#eval fourAndThree.modifyBoth Float.floor

structure RectangularPrism where 
   height : Float
   width  : Float
   depth  : Float

def volumePrism (p : RectangularPrism) : Float := p.height * p.width * p.depth

structure Segment where
  p1 : Point
  p2 : Point

def length (l : Segment) : Float := distance l.p1 l.p2

/- Which names are introduced by the declaration of RectangularPrism? -/
/- p.height, p.width, p.depth, p.mk -/

/- Which names are introduced by the following declarations of Hamster and Book? What are their types? -/

structure Hamster where
  name : String
  fluffy : Bool
  
structure Book where
  makeBook ::
  title : String
  author : String
  price : Float

inductive MyBool where
  | false : MyBool
  | true  : MyBool

inductive MyNat where
  | zero 
  | succ (n : Nat)

#eval Nat.succ Nat.zero
#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))

def isZero (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ _ => false

#eval isZero 0
#eval isZero 5

def pred (n : Nat) : Nat :=
  match n with
  | Nat.zero   => Nat.zero
  | Nat.succ k => k

#eval pred 0
#eval pred 5
#eval pred 839

def depth (p : Point3D) : Float :=
  match p with
  | { x := _h,
      y := _w,
      z :=  d } => d

#eval depth origin3D 

def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (even k)

def evenLoops (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not (evenLoops n)

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => Nat.succ (plus n k')

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => Nat.zero
  | Nat.succ k' => plus n (times n k')

def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero => n
  | Nat.succ k' => pred (minus n k')

def div (n : Nat) (k : Nat) : Nat :=
  if n < k then
    0
  else Nat.succ (div (n - k) k)
