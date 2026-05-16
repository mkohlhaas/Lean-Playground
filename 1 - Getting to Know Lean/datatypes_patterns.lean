-- from previous chapters

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

/- ---------------------- -/
/- Datatypes and Patterns -/
/- ---------------------- -/

-- product type       = collection of values (structure)
-- sum type           = allows choices
-- recursive datatype = datatype that can include instances of themselves (e.g. lists, trees, …)
-- inductive datatype = recursive sum type - consumed through pattern matching and recursive functions

-- many of the built-in types are actually inductive datatypes in the standard library

-- Bool has two constructors, false and true.
-- In the Lean standard library, true and false are re-exported from the Bool namespace so that they can be written alone, rather than as Bool.true and Bool.false.
inductive MyBool where
  | false : MyBool
  | true  : MyBool

#print Bool                                             

inductive MyNat where
  | zero 
  | succ (n : Nat)

#print Nat                                              

#check (Nat.succ)                                       

#eval Nat.succ Nat.zero                                 
#eval Nat.succ (Nat.succ (Nat.succ (Nat.succ Nat.zero)))
#eval Nat.succ $ Nat.succ $ Nat.succ $ Nat.succ Nat.zero

/- ---------------- -/
/- Pattern Matching -/
/- ---------------- -/

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

-- pattern matching also works with structures
def depth (p : Point3D) : Float :=
  match p with
  | { x := _h,                                          
      y := _w,
      z :=  d } => d

#eval depth origin3D                                    

-- easier in this case
def depth' (p : Point3D) : Float :=
  Point3D.z p
  
#eval depth' origin3D                                   

/- ------------------- -/
/- Recursive Functions -/
/- ------------------- -/

-- structural recursion
def even (n : Nat) : Bool :=
  match n with
  | Nat.zero   => true
  | Nat.succ k => not $ even k

-- Lean doesn't accept recursions which attempt to invoke itself on the original number
def evenLoops (n : Nat) : Bool :=                      
  match n with
  | Nat.zero   => true
  | Nat.succ k => not $ evenLoops n

def plus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => Nat.succ $ plus n k'

def times (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => Nat.zero
  | Nat.succ k' => plus n $ times n k'

-- subtraction n−k takes n's predecessor k times
def minus (n : Nat) (k : Nat) : Nat :=
  match k with
  | Nat.zero    => n
  | Nat.succ k' => pred $ minus n k'

def div (n : Nat) (k : Nat) : Nat :=                  
  if n < k
    then 0
    else Nat.succ $ div (n - k) k

