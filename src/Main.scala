import ModelChecker._
import sharedOBDDs._

object Main extends App {
  //val formula = And(Atom(1), Atom(2))
  val formula = And(Atom(2), Or(Atom(3), Atom(1))) //:(
  //val formula = Or(Atom(3), And(Atom(2), Atom(1))) //:(
  //val formula = Or(Atom(2), Atom(1))
  //val formula = And(Top(), Bottom())
  //val formula = And (Atom(3), Atom(1))
  val s1 = Conjunction(Variable(1), Conjunction(Variable(2), Negation(Variable(3))))
  val s2 = Conjunction(Variable(2), Conjunction(Variable(3), Negation(Variable(1))))
  val s3 = Conjunction(Variable(3), Conjunction(Negation(Variable(1)), Negation(Variable(2))))
  val transitions = False
  val states = Disjunction(s1, Disjunction(s2, s3))

  //TODO use one bdd for states and transitions??
  val bddStates = build(new BDD(initT(3), initH(), 2), states)
  val bddTransitions = build(new BDD(initT(3), initH(), 2), transitions)
  val result = sat(bddStates, bddTransitions, formula)

  println(evaluate(result._1, result._2, Map(1 -> true, 2 -> true, 3 -> false))) // s1
  println(evaluate(result._1, result._2, Map(1 -> false, 2 -> true, 3 -> true))) // s2
  println(evaluate(result._1, result._2, Map(1 -> false, 2 -> false, 3 -> true))) // s3

}

