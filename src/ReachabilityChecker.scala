import leon.collection._
import leon.lang._
import leon.annotation._
import leon.proof._

import scala.language.postfixOps

import sharedOBDDs._

object ReachabilityChecker {
  
  def reachable(b: BDD, transitions: BigInt, initialStates: BigInt, targetStates: BigInt) : Boolean = {
    if(intersect(b, initialStates, targetStates).root != 0)
      true
    else {
      val next = post(b, initialStates, transitions)
      val reached = union(next.b, initialStates, next.root)
      if(reached.root == initialStates) //fixed point
        false
      else
        reachable(reached.b, transitions, reached.root, targetStates)
    }
  }

}
