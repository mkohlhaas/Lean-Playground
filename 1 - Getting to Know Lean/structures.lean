/- ---------- -/
/- Structures -/
/- ---------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=structures

#check 1.2                                                   
#check -454.2123215                                          
#check 0.0                                                   

#check  0                                                    
#check (0 : Float)                                           

structure Point where
  x : Float
  y : Float
deriving Repr

def origin   : Point := { x := 0.0, y := 0.0 }
def origin'          := { x := 0.0, y := 0.0 }               
def origin''         := { x := 0.0, y := 0.0 : Point}

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
  Float.sqrt $ (p2.x - p1.x) ^ 2.0 + (p2.y - p1.y) ^ 2.0

#eval distance { x := 1.0, y := 2.0 } { x := 5.0, y := -1.0 }
#eval distance p1 p2                                         

structure Point3D where
  x : Float
  y : Float
  z : Float

def origin3D : Point3D := { x := 0.0, y := 0.0, z := 0.0 }

-- Lean also allows the structure type annotation inside the curly braces.
#check ({ x := 0.0, y := 0.0 } : Point)                      
#check  { x := 0.0, y := 0.0   : Point}                      

/- ------------------- -/
/- Updating Structures -/
/- ------------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=updating-structures

def zeroX1 (p : Point) : Point := { x := 0, y := p.y }
def zeroX2 (p : Point) : Point := { p with x := 0 }

def fourAndThree : Point := { x := 4.3, y := 3.4 }

-- structure updates do not modify the original structure
#eval fourAndThree                                           
#eval zeroX1 fourAndThree                                    
#eval zeroX2 fourAndThree                                    
#eval fourAndThree                                           

/- ----------------- -/
/- Behind the Scenes -/
/- ----------------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=behind-the-scenes

#print Point                                                 

-- constructor (not good Lean style)
#eval  Point.mk 1.5 2.8                                      
#check Point.mk 1.5 2.8                                      

-- constructor and accessor functions
#check (Point.mk)                                            
#check (Point.x)                                             
#check (Point.y)                                             

#eval Point.x origin                                         
#eval origin.x                                               

structure MyPoint where
  point ::                                                        -- new constructor name
  x : Float
  y : Float

#print MyPoint                                               

#eval  MyPoint.point 1.5 2.8                                 
#check MyPoint.point 1.5 2.8                                 

-- accessor dot notation 
#check String.append                                         
#eval "one string".append " and another"                     
#eval String.append "one string" " and another"              

def Point.modifyBoth (f : Float → Float) (p : Point) : Point :=
  { x := f p.x, y := f p.y }

-- accessor dot notation
-- NOTE: Point is NOT the first argument!
#eval  fourAndThree.modifyBoth Float.floor                   

/- --------- -/
/- Exercises -/
/- --------- -/

-- https://lean-lang.org/functional_programming_in_lean/find/?domain=Verso.Genre.Manual.section&name=structure-exercises

structure RectangularPrism where 
  height : Float
  width  : Float
  depth  : Float

def rectPrism : RectangularPrism := {height := 5., width := 4., depth := 2.}

def volumePrism (p : RectangularPrism) : Float :=
  p.height * p.width * p.depth

-- with pattern matching
def volumePrism' : RectangularPrism -> Float 
  | {height, width, depth} => height * width * depth

def RectangularPrism.volume := volumePrism'

#check (volumePrism)                                        
#check (RectangularPrism.volume)                            

#check 5.                                                   
#eval volumePrism  rectPrism                                
#eval volumePrism' rectPrism                                
#eval rectPrism.volume                                      

structure Segment where
  p1 : Point
  p2 : Point
deriving Repr

#print Segment                                              

def segmentLength (l : Segment) : Float := distance l.p1 l.p2
def Segment.length := segmentLength

def P1 := {x := 0., y := 1. : Point}
def P2 := {x := 1., y := 0. : Point}
def S  := {p1 := P1, p2 := P2 : Segment}

#check (segmentLength)                                      
#eval S                                                     
#eval segmentLength {p1 := P1, p2 := P2}                    
#eval {p1 := P1, p2 := P2 : Segment}.length                 
#eval S.length                                              

-- Which names are introduced by the declaration of RectangularPrism?
-- p.height, p.width, p.depth, p.mk

-- Which names are introduced by the following declarations of Hamster and Book? What are their types?

structure Hamster where
  name   : String
  fluffy : Bool
  
structure Book where
  makeBook ::
  title  : String
  author : String
  price  : Float

#print Hamster                                             
#print Book                                                
