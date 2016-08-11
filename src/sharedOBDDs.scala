import leon.collection._
import leon.lang._

//shared BDDs
//in this approach all obdds are stored in the same tables T, H => memory leak! -> garbage collector on tables would be useful
object sharedOBDDs {
  case class BDD(T: Map[BigInt, (BigInt, BigInt, BigInt)], H: Map[(BigInt, BigInt, BigInt), BigInt], size: BigInt)

  abstract class Expression
  case object Top extends Expression
  case object Bottom extends Expression
  case class Variable(i: BigInt) extends Expression
  case class Negation(e: Expression) extends Expression
  case class Conjunction(e1: Expression, e2: Expression) extends Expression
  case class Disjunction(e1: Expression, e2: Expression) extends Expression

  def initT(numberOfVars: BigInt): Map[BigInt, (BigInt, BigInt, BigInt)] = {
    Map(BigInt(0) -> (numberOfVars + 1, BigInt(-1), BigInt(-1)), BigInt(1) -> (numberOfVars + 1, BigInt(-1), BigInt(-1)))
  }

  def initH(): Map[(BigInt, BigInt, BigInt), BigInt] = Map()

  //smarter allocation scheme for ids needed?
  def add(b: BDD, i: BigInt, l: BigInt, h: BigInt): BDD = {
    new BDD(b.T + (b.size -> (i, l, h)), b.H + ((i, l, h) -> b.size), b.size + 1)
  }

  def variable(b: BDD, node: BigInt): BigInt = b.T(node)._1
  def low(b: BDD, node: BigInt): BigInt = b.T(node)._2
  def high(b: BDD, node: BigInt): BigInt = b.T(node)._3

  def testAndInsert(b: BDD, i: BigInt, l: BigInt, h: BigInt): (BDD, BigInt) = {
    if (l == h)
      (b, l)
    else if (b.H.contains((i, l, h)))
      (b, b.H((i, l, h)))
    else {
      val bNew = add(b, i, l, h)
      (bNew, b.size) //adapt if allocation scheme for IDs changes!
    }
  }
  
  //proof: see leon example 
  def restrictExpression(e: Expression, i: BigInt, value: Expression): Expression = {
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

  def build(b: BDD, e: Expression): (BDD, BigInt) = {
    val n = maxVarLabel(e, 0) //assumption: variables are labelled with integers starting from 1
    def buildRec(b1: BDD, e: Expression, i: BigInt): (BDD, BigInt) = {
      if (i > n) {
        e match { // no more variables -> only constants possible
          case Top  => (b1, 1)
          case Bottom => (b1, 0)
        }
      } else {
        val r1 = buildRec(b1, restrictExpression(e, i, Bottom), i + 1)
        val r2 = buildRec(r1._1, restrictExpression(e, i, Top), i + 1)
        testAndInsert(r2._1, i, r1._2, r2._2)
      }
    }

    buildRec(b, e, 1)
  }

  def maxVarLabel(e: Expression, max: BigInt): BigInt = {
    e match {
      case Top         => 0
      case Bottom        => 0
      case Variable(i)  => if (i > max) i else max
      case Negation(e1) => maxVarLabel(e1, max)
      case Conjunction(e1, e2) => {
        val max1 = maxVarLabel(e1, max)
        maxVarLabel(e2, max1)
      }
      case Disjunction(e1, e2) => {
        val max1 = maxVarLabel(e1, max)
        maxVarLabel(e2, max1)
      }

    }
  }

  //no dynamic programming used here in order to stay purely functional
  def apply(b: BDD, op: (Boolean, Boolean) => Boolean, r1: BigInt, r2: BigInt): (BDD, BigInt) = {
    if ((r1 == 0 || r1 == 1) && (r2 == 0 || r2 == 1)) //two Terminals
      if (op(r1 == 1, r2 == 1)) (b, 1) else (b, 0)
    else if (variable(b, r1) == variable(b, r2)) {
      val loApp = apply(b, op, low(b, r1), low(b, r2))
      val hiApp = apply(loApp._1, op, high(b, r1), high(b, r2))
      testAndInsert(hiApp._1, variable(b, r1), loApp._2, hiApp._2)
    } else if (variable(b, r1) < variable(b, r2)) {
      val loApp = apply(b, op, low(b, r1), r2)
      val hiApp = apply(loApp._1, op, high(b, r1), r2)
      testAndInsert(hiApp._1, variable(b, r1), loApp._2, hiApp._2)
    } else {
      val loApp = apply(b, op, r1, low(b, r2))
      val hiApp = apply(loApp._1, op, r1, high(b, r2))
      testAndInsert(hiApp._1, variable(b, r2), loApp._2, hiApp._2)
    }

  }

  def union(b: BDD, r1: BigInt, r2: BigInt) = apply(b, _ || _, r1, r2)
  def intersect(b: BDD, r1: BigInt, r2: BigInt) = apply(b, _ && _, r1, r2)

  def minus(b: BDD, r1: BigInt, r2: BigInt) = {
    val bNew = complement(b, r2)
    intersect(bNew._1, r1, bNew._2)
  }

  def complement(b: BDD, root: BigInt): (BDD, BigInt) = apply(b, _ != _, root, 1)

  def equivalent(r1: BigInt, r2: BigInt) = r1 == r2


  //TODO use restrict algo instead??
  //precond: all variables in map 
  def evaluate(b: BDD, root: BigInt, interpretaion: Map[BigInt, Boolean]): Boolean = {
    if (root == 1)
      true
    else if (root == 0)
      false
    else {
      if (interpretaion(variable(b, root)))
        evaluate(b, high(b, root), interpretaion)
      else
        evaluate(b, low(b, root), interpretaion)
    }
  }

  def restrict(b: BDD, root: BigInt, eliminatedVar: BigInt, value: Boolean): (BDD, BigInt) = {
    if (variable(b, root) > eliminatedVar)
      (b, root)
    else if (variable(b, root) < eliminatedVar) {
      val lo = restrict(b, low(b, root), eliminatedVar, value)
      val hi = restrict(lo._1, high(b, root), eliminatedVar, value)
      testAndInsert(b, variable(b, root), lo._2, hi._2)
    } else if (value) //variable(b, root) == eliminatedVar
      restrict(b, high(b, root), eliminatedVar, value)
    else
      restrict(b, low(b, root), eliminatedVar, value)
  }

  def exists(b: BDD, root: BigInt, consideredVar: BigInt): (BDD, BigInt) = {
    val resToZero = restrict(b, root, consideredVar, false)
    val resToOne = restrict(resToZero._1, root, consideredVar, true)
    apply(resToOne._1, _ || _, resToZero._2, resToOne._2)
  }

  //precond: lists nonempty + same size
  def rename(b: BDD, root: BigInt, oldNames: List[BigInt], newNames: List[BigInt]): (BDD, BigInt) = {
    if (root == 0 || root == 1)
      (b, root)
    else {
      val lo = rename(b, low(b, root), oldNames, newNames)
      val hi = rename(lo._1, high(b, root), oldNames, newNames)
      
      val name = if (oldNames.contains(variable(b, root))) newNames(oldNames.indexOf(variable(b, root)))
      else variable(b, root)

      testAndInsert(hi._1, name, lo._2, hi._2)
    }
  }

  //TODO implement
  def preE(b: BDD, root: BigInt, transitions: BDD, rootTrans: BigInt): (BDD, BigInt) = (b, root)
    //val bPrimed = rename(b, )//TODO this is inefficient -> unprimed and primed variables should be interleaved
  

  def preA(b: BDD, root: BigInt, rootX: BigInt, transitions: BDD, transRoot: BigInt): (BDD, BigInt) = {
    val complementSet = minus(b, root, rootX)
    val preExists = preE(complementSet._1, complementSet._2, transitions, transRoot)
    minus(preExists._1, root, preExists._2)
  }

}
