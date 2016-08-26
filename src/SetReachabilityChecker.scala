import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

import scala.language.postfixOps

object SetReachabilityChecker {

  case class State(registers: List[Boolean])
  
  case class System(nrOfRegisters: BigInt, transitions: List[(State, State)])
  
  abstract class Result
  case object Unknown extends Result
  case object Unreachable extends Result
  case class Trace(states: List[State]) extends Result

  //is maintaining a map a good idea or would it be better to store predeccessor in state?
  def kReachabilityCheck(s: System, initial: List[State], target: State, pre: Map[State, State], k: BigInt) : Result = {
    if(initial.contains(target))
      Trace(getTrace(pre, target))
    else if(k == 0)
      Unknown
    else {
      //TODO implement set operations for lists (e.g. with sorted lists)
      val p = post(s, initial, pre)
      val next = p._1 ++ initial
      if(next.content == initial.content) //is this a good way of checking equality?
        Unreachable
      else
        kReachabilityCheck(s, next, target, p._2, k - 1)
    }  
  }
  
  def getTrace(pre: Map[State, State], s: State) : List[State] = {
    if(!pre.contains(s))
      List(s)
    else
      s :: getTrace(pre, pre(s))
  }
  
  def post(s: System, states: List[State], pre: Map[State, State]) : (List[State], Map[State, State]) = {
    states match {
      case Nil() => (List(), pre)
      case x :: xs => {
        val succ = successors(s.transitions, x, pre)
        val p = post(s, xs, succ._2)
        (succ._1 ++ p._1, p._2)
      }
    }
  }
  
  def successors(tr: List[(State, State)], s: State, pre: Map[State, State]) : (List[State], Map[State, State]) = {
    tr match {
      case Nil() => (List(), pre)
      case Cons((s1,s2), trs) =>
        if (s1 == s) {
          val succ = successors(trs, s, pre.updated(s2, s1))
          (Cons(s2, succ._1), succ._2) //if s2 already in map it wouldn't have to be added to list-> adapt?
        } else
          successors(trs, s, pre)
    }
  } 
  
}
