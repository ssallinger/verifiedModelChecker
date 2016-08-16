import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

object sharedOBDDs {

  case class Node(variable: BigInt, low: BigInt, high: BigInt)
  case class BDD(nodes: List[BigInt], T: Map[BigInt, Node], H: Map[Node, BigInt], size: BigInt)
  case class RootedBDD(b: BDD, root: BigInt)

  abstract class Expression
  case object Top extends Expression
  case object Bottom extends Expression
  case class Variable(i: BigInt) extends Expression
  case class Negation(e: Expression) extends Expression
  case class Conjunction(e1: Expression, e2: Expression) extends Expression
  case class Disjunction(e1: Expression, e2: Expression) extends Expression
 
  //create new Table containing the terminal nodes (ID 0 and 1)
  def initT(numberOfVars: BigInt): Map[BigInt, Node] = {
    Map(BigInt(0) -> Node(numberOfVars + 1, BigInt(-1), BigInt(-1)), BigInt(1) -> Node(numberOfVars + 1, BigInt(-1), BigInt(-1)))
  }

  def initH(): Map[Node, BigInt] = Map()

  //Map m is wellformed if it contains all elements of List l
  def wellFormed[X,Y](l: List[X], m: Map[X,Y]): Boolean = l match {
    case Nil() => true
    case Cons(x, xs) => m.contains(x) && wellFormed(xs,m)
  }
  
  //updating a map preserves property of being wellformed
  @induct
  def wellFormedUpdate[X,Y](l: List[X], m: Map[X,Y], x: X, y: Y): Boolean = {
    require(wellFormed(l,m))
    
    wellFormed(x :: l, m.updated(x,y))
  } holds 
  
  def add(b: BDD, n: Node): BDD = {
    //smarter allocation scheme for ids needed?
    BDD(b.size :: b.nodes, b.T.updated(b.size, n), b.H.updated(n, b.size), b.size + 1)
  }
  
  //add preserves wellformedness
  def wellFormedAdd(b: BDD, n: Node): Boolean = {
    require(wellFormed(b.nodes,b.T))
    
    val res = add(b, n)
    b.nodes.content.subsetOf(res.nodes.content) &&
    wellFormedUpdate(b.nodes, b.T, b.size, n) &&
    wellFormed(res.nodes, res.T)
  } holds
  
  def getNode(b: BDD, id: BigInt): Node = {
    require(b.T.contains(id))
    b.T(id)
  }
  
  //look for node and create it if it does not exist
  def testAndInsert(b: BDD, n: Node): RootedBDD = {
    if (n.low == n.high)
      RootedBDD(b, n.low)
    else if (b.H.contains(n))
      RootedBDD(b, b.H(n))
    else {
      RootedBDD(add(b, n), b.size) //adapt if allocation scheme for IDs changes!
    }
  }
  
  def wellFormedTestAndInsert(b: BDD, n: Node) : Boolean = {
    require(wellFormed(b.nodes, b.T))
    
    val res = testAndInsert(b, n)
    b.nodes.content.subsetOf(res.b.nodes.content) &&
    wellFormedAdd(b, n) &&
    wellFormed(res.b.nodes, res.b.T)
  } holds

  def isConstant(e: Expression) : Boolean = e match {
    case Top => true
    case Bottom => true
    case _ => false
  }
  
  
  //restricts Expression by replacing variable with id i by value (should be Top or Bottom) and simplifying
  def restrictExpression(e: Expression, i: BigInt, value: Expression): Expression = {
  	require(isConstant(value))
    e match {
      case Top        => Top
      case Bottom       => Bottom
      case Variable(j) => if (i == j) value else e
      case Conjunction(e1, e2) => {
        val e1New = restrictExpression(e1, i, value)
        val e2New = restrictExpression(e2, i, value)
        e1New match {
          case Top  => e2New
          case Bottom => Bottom
          case _ => e2New match {
            case Top  => e1New
            case Bottom => Bottom
            case _     => Conjunction(e1New, e2New)
          }
        }
      }
      case Disjunction(e1, e2) => {
        val e1New = restrictExpression(e1, i, value)
        val e2New = restrictExpression(e2, i, value)
        e1New match {
          case Top  => Top
          case Bottom => e2New
          case _ => e2New match {
            case Top  => Top
            case Bottom => e1New
            case _     => Disjunction(e1New, e2New)
          }
        }
      }
      case Negation(e1) => {
        val e1New = restrictExpression(e1, i, value)
        e1New match {
          case Top         => Bottom
          case Bottom        => Top
          case Negation(e2) => e2
          case _            => Negation(e1New)
        }
      }
    }
  }

  def build(b: BDD, e: Expression): RootedBDD = {
    val n = maxVarLabel(e)
    def buildRec(b1: BDD, e: Expression, i: BigInt): RootedBDD = {
//       require(e == restrictExpression(
      if (i > n) {
        e match { // no more variables -> only constants possible
          case Top  => RootedBDD(b1, 1)
          case Bottom => RootedBDD(b1, 0)
        }
      } else {
        val RootedBDD(bdd1, r1) = buildRec(b1, restrictExpression(e, i, Bottom), i + 1)
        val RootedBDD(bdd2, r2) = buildRec(bdd1, restrictExpression(e, i, Top), i + 1)
        testAndInsert(bdd2, Node(i, r1, r2))
      }
    }

    buildRec(b, e, 1)
  }

  def maxVarLabel(e: Expression): BigInt = {
    e match {
      case Top          => 0
      case Bottom       => 0
      case Variable(i)  => i
      case Negation(e1) => maxVarLabel(e1)
      case Conjunction(e1, e2) => {
        val max1 = maxVarLabel(e1)
        val max2 = maxVarLabel(e2)
        if(max1 > max2) max1 else max2
      }
      case Disjunction(e1, e2) => {
        val max1 = maxVarLabel(e1)
        val max2 = maxVarLabel(e2)
        if(max1 > max2) max1 else max2
      }
    }
  }
  
  def containsAllChildren(b: BDD, r: BigInt): Boolean = {
    b.T.contains(r) &&
    containsAllChildren(b, getNode(b,r).low) &&
    containsAllChildren(b, getNode(b,r).high) 
  }
  
  def allChildrenInSet(b: BDD, r: BigInt, s: List[BigInt]): Boolean = {
    s.contains(r) &&
    allChildrenInSet(b, getNode(b,r).low, s) &&
    allChildrenInSet(b, getNode(b,r).high, s) 
  }
  
  def apply(b: BDD, op: (Boolean, Boolean) => Boolean, r1: BigInt, r2: BigInt): RootedBDD = {
    //require(containsAllChildren(b, r1) && containsAllChildren(b, r2) && wellFormed(b.nodes, b.T))
  
    if ((r1 == 0 || r1 == 1) && (r2 == 0 || r2 == 1)) //two Terminals
      if (op(r1 == 1, r2 == 1)) RootedBDD(b, BigInt(1)) 
      else RootedBDD(b, BigInt(0))
    else if (getNode(b, r1).variable == getNode(b, r2).variable) {
      val RootedBDD(bLow, rLow) = apply(b, op, getNode(b, r1).low, getNode(b, r2).low)
      // b.nodes subset of loApp.nodes
      val RootedBDD(bHigh, rHigh) = apply(bLow, op, getNode(b, r1).high, getNode(b, r2).high)
      testAndInsert(bHigh, Node(getNode(b, r1).variable, rLow, rHigh))
    } 
//     else (b,r1)
    else if (getNode(b, r1).variable < getNode(b, r2).variable) {
      val RootedBDD(bLow, rLow) = apply(b, op, getNode(b, r1).low, r2)
      val RootedBDD(bHigh, rHigh) = apply(bLow, op, getNode(b, r1).high, r2)
      testAndInsert(bHigh, Node(getNode(b, r1).variable, rLow, rHigh))
    } else {
      val RootedBDD(bLow, rLow) = apply(b, op, r1, getNode(b, r2).low)
      val RootedBDD(bHigh, rHigh) = apply(bLow, op, r1, getNode(b, r2).high)
      testAndInsert(bHigh, Node(getNode(b, r2).variable, rLow, rHigh))
    }

  } /*ensuring ((res: RootedBDD) => {
    val RootedBDD(bdd,r) = res
    b.nodes.content.subsetOf(bdd.nodes.content) &&
    wellFormed(bdd.nodes, bdd.T)
  })*/
//     containsAllChildren(bdd,r) &&
//     bdd.wellFormed()
//   })

  //TODO prove
  def correctApplyOr(b: BDD, f: Expression, g: Expression, rf: BigInt, rg: BigInt) : Boolean = {
    require(represents(b, rf, f) && represents(b, rg, g))
    val res = apply(b, _ || _, rf, rg)
    represents(res.b, res.root, Conjunction(f, g)) because {
      if((rf == 0 || rf == 1) && (rg == 0 || rg == 1))
        trivial
      else if (getNode(b, rf).variable == getNode(b, rg).variable) {
        val v = getNode(b, rf).variable
        restrictRepresentsChildren(b, rf, f) && //for precondition of I.H.
        restrictRepresentsChildren(b, rg, g) &&
        correctApplyOr(b, //I.H.
                       restrictExpression(f, v, Bottom),
                       restrictExpression(g, v, Bottom),
                       getNode(b, rf).low,
                       getNode(b, rg).low) &&
        correctApplyOr(b,//I.H.
                       restrictExpression(f, v, Top),
                       restrictExpression(g, v, Top),
                       getNode(b, rf).high,
                       getNode(b, rg).high) &&
        shannonExpansionEquivalence(b, f, v) &&
        represents(res.b, res.root, shannonExpansion(f, v)) //&&
        //testand insert of node repr. shannon expansion
                       
      }
      else trivial//TODO
    }
  } holds
  
  def shannonExpansion(e: Expression, v: BigInt) = {
    Disjunction(Conjunction(Negation(Variable(v)), restrictExpression(e, v, Bottom)), Conjunction(Variable(v), restrictExpression(e, v, Top)))
  }
  
  //TODO prove
  def shannonExpansionEquivalence(b: BDD, e: Expression, v: BigInt) = {
    build(b, e).root == build(b, shannonExpansion(e, v)).root
  } holds
  
  def represents(b: BDD, root: BigInt, e: Expression) : Boolean = {
    build(b, e).root == root
  }
  
  //TODO prove
  def restrictRepresentsChildren(b: BDD, root: BigInt, e: Expression) = {
    require(represents(b, root, e))
    represents(b, getNode(b, root).low, restrictExpression(e, getNode(b, root).variable, Bottom)) &&
    represents(b, getNode(b, root).high, restrictExpression(e, getNode(b, root).variable, Bottom))
  } holds
  
  def union(b: BDD, r1: BigInt, r2: BigInt) = apply(b, _ || _, r1, r2)
  def intersect(b: BDD, r1: BigInt, r2: BigInt) = apply(b, _ && _, r1, r2)

  def minus(b: BDD, r1: BigInt, r2: BigInt) = {
    val bNew = complement(b, r2)
    intersect(bNew.b, r1, bNew.root)
  }

  def complement(b: BDD, root: BigInt) = apply(b, _ != _, root, 1)

  def equivalent(r1: BigInt, r2: BigInt) = r1 == r2


  //use restrict algo instead?
  //precond: all variables in map 
  def evaluate(bdd: RootedBDD, interpretaion: Map[BigInt, Boolean]): Boolean = {
    if (bdd.root == 1)
      true
    else if (bdd.root == 0)
      false
    else {
      if (interpretaion(getNode(bdd.b, bdd.root).variable))
        evaluate(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).high), interpretaion)
      else
        evaluate(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).low), interpretaion)
    }
  }

  def restrict(bdd: RootedBDD, eliminatedVar: BigInt, value: Boolean): RootedBDD = {
    if (getNode(bdd.b, bdd.root).variable > eliminatedVar)
		bdd
    else if (getNode(bdd.b, bdd.root).variable < eliminatedVar) {
      val RootedBDD(bLow, rLow) = restrict(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).low), eliminatedVar, value)
      val RootedBDD(bHigh, rHigh) = restrict(RootedBDD(bLow, getNode(bdd.b, bdd.root).high), eliminatedVar, value)
      testAndInsert(bHigh, Node(getNode(bdd.b, bdd.root).variable, rLow, rHigh))
    } else if (value) //variable(b, root) == eliminatedVar
      restrict(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).high), eliminatedVar, value)
    else
      restrict(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).low), eliminatedVar, value)
  }

  def exists(bdd: RootedBDD, consideredVar: BigInt): RootedBDD = {
    val RootedBDD(b0, r0) = restrict(bdd, consideredVar, false)
    val RootedBDD(b1, r1)  = restrict(RootedBDD(b0, bdd.root), consideredVar, true)
    apply(b1, _ || _, r0, r1)
  }

  //precond: lists nonempty + same size
  def rename(bdd: RootedBDD, oldNames: List[BigInt], newNames: List[BigInt]): RootedBDD = {
    if (bdd.root == 0 || bdd.root == 1)
      bdd
    else {
      val RootedBDD(bLow, rLow) = rename(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).low), oldNames, newNames)
      val RootedBDD(bHigh, rHigh) = rename(RootedBDD(bLow, getNode(bdd.b, bdd.root).high), oldNames, newNames)
      
      val name = if (oldNames.contains(getNode(bdd.b, bdd.root).variable)) newNames(oldNames.indexOf(getNode(bdd.b, bdd.root).variable))
      else getNode(bdd.b, bdd.root).variable

      testAndInsert(bHigh, Node(name, rLow, rHigh))
    }
  }

  //TODO implement
  def preE(statesSubset: RootedBDD, transitions: RootedBDD): RootedBDD = statesSubset
    //val bPrimed = rename(b, )//TODO this is inefficient -> unprimed and primed variables should be interleaved
  

  def preA(states: RootedBDD, rootSubset: BigInt, transitions: RootedBDD): RootedBDD = {
    val complement = minus(states.b, states.root, rootSubset)
    val RootedBDD(bPreE, rPreE) = preE(complement, transitions)
    minus(bPreE, states.root, rPreE)
  }
  
  def extend(s: Set[List[Boolean]], i: BigInt): Set[List[Boolean]] = {
    if(i == 0)
      s
    else
      extend(setToList(s).map(l => false::l).content ++ setToList(s).map(l => true::l).content, i - 1)
  }
  
  def contentLists(bdd: RootedBDD) : Set[List[Boolean]] = {
    if(bdd.root == 0)
      Set()
    else if(bdd.root == 1)
      Set(List[Boolean]())
    else {
      val lo = if(getNode(bdd.b, bdd.root).variable - getNode(bdd.b, getNode(bdd.b, bdd.root).low).variable == 1)
                 contentLists(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).low))
               else
                 extend(contentLists(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).low)),
                   getNode(bdd.b, bdd.root).variable - getNode(bdd.b, getNode(bdd.b, bdd.root).low).variable - 1)
      val hi = if(getNode(bdd.b, bdd.root).variable - getNode(bdd.b, getNode(bdd.b, bdd.root).high).variable == 1)
                 contentLists(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).high))
               else
                 extend(contentLists(RootedBDD(bdd.b, getNode(bdd.b, bdd.root).high)),
                   getNode(bdd.b, bdd.root).variable - getNode(bdd.b, getNode(bdd.b, bdd.root).high).variable - 1)
      setToList(lo).map(l => false::l).content ++ setToList(hi).map(l => true::l).content
    }
  }
  
  /*def content(b: BDD, root: BigInt) : Set[State] = {
    setToList(contentLists(b, root)).map(l => State(l)).content
  }*/
  
  def correctUnion(b: BDD, root1: BigInt, root2: BigInt) : Boolean = {
  	val bddUnion = union(b, root1, root2)
  	(contentLists(bddUnion) == contentLists(RootedBDD(b, root1)) ++ contentLists(RootedBDD(b, root2)))
  } holds
}
