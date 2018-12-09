
package breu;

import org.sat4j.tools.GateTranslator
import org.sat4j.minisat.SolverFactory
import org.sat4j.specs.ISolver
import org.sat4j.core.VecInt

import scala.collection.mutable.{Set => MSet, ListBuffer}


class LazySolver[Term, Fun](
  timeoutChecker : () => Unit,
  maxSolverRuntime : Long,
  debug : Boolean = false
) extends Solver[Term, Fun](timeoutChecker, maxSolverRuntime, debug) {

  case class LazySolverException(msg : String) extends RuntimeException(msg)

  // Solve the  problem by:
  // (1) Generate a random assignments A
  // (2) Check if A is a solution to the problem
  // (2a) if NO, go to (3)
  // (2b) if YES, terminate with A
  // (3) Generate blocking clause B that excludes A
  // (4) Add B to the constraints and generate new assignment A'
  // (5) Let A = A' and go to (2)
  override def solveaux(problem : Problem)
      : (breu.Result.Result, Option[Map[Int, Int]]) =
    Timer.measure("LazySolver.solveaux") {
      reset
      bcCount = 0

      val assignments = createAssignments(problem)

      // Used to store what bits are equivalent to term equal term
      val teqt = Array.fill[Int](problem.terms.length, problem.terms.length)(-1)

      // Keeps track whether a subproblem has triggered UNSAT
      val blockingProblem = Array.ofDim[Boolean](problem.size)
      unitClauses.clear

      def handleBlockingProblem(cp : SubProblem, solution : Map[Int, Int]) =
        Timer.measure("handleBlockingProblem") {
          // val DQ = new Disequalities(cp.DQ)
          val DQ = new Disequalities(cp.terms.max+1, cp.funEqs.toArray, timeoutChecker)

          // Could we replace this by just doing cascade-remove on the assignments?
          val uf = Util.BreunionFind(cp.terms, List(), solution.toList)

          // TODO: Can we change this to if (s < t) ...
          for (s <- cp.terms; t <- cp.terms;
            if (s <= t); if (uf(s) == uf(t))) {
            DQ.cascadeRemove(s, t)
          }

          def heuristic(dq : (Int, Int)) = {
            val (s, t) = dq
            cp.domains(s).size
          }

          // Now we minimize DI to only contain "relevant" inequalities
          DQ.minimise(cp.terms, cp.goal.subGoals, heuristic)

          // Remove all "base" inequalities, since they will always be there
          val ineqs = DQ.inequalities(cp.terms)
          val finalDQ = for ((s,t) <- ineqs; if cp.baseDQ(s, t)) yield (s, t)

          // Replace with assertions
          assert(!DQ.satisfies(cp.goal.subGoals), "Minimization failed")

          // TODO: Maybe we can do this more efficient

          val blockingClause =
            (for ((s,t) <- finalDQ) yield {
              if (teqt(s min t)(s max t) == -1)
                teqt(s min t)(s max t) =
                  termEqTermAux(assignments(s), assignments(t))
              teqt(s min t)(s max t)
            }).toArray

          if (finalDQ.length == 1) {
            val (s,t) = finalDQ(0)
            unitClauses += ((s,t))
          }

          try {
            positiveBlockingClauses += finalDQ.toList            
            solver.addClause(new VecInt(blockingClause))
            bcCount += 1
            false
          } catch {
            case e : org.sat4j.specs.ContradictionException => {
              true
            }
          }
        }

      // If all problems are SAT or one problem is infeasible, we are done
      var allSat = false
      var infeasible = false
      var candidate = Map() : Map[Int, Int]

      // Check the "hardest" problem first!
      var problemOrder = List.tabulate(problem.size)(x => x)


      // Add given blocking clauses
      for (bc <- problem.positiveBlockingClauses) {
        dprintln("Lazy>+BC: " + bc)
        val blockingClause =
          (for ((s,t) <- bc) yield {
            if (teqt(s min t)(s max t) == -1)
              teqt(s min t)(s max t) =
                termEqTermAux(assignments(s), assignments(t))
            teqt(s min t)(s max t)
          }).toArray

        try {
          positiveBlockingClauses += bc.toList
          solver.addClause(new VecInt(blockingClause))
          bcCount += 1
        } catch {
          case e : org.sat4j.specs.ContradictionException => {
            throw new Exception("Blocking Clauses are Contradictory")
          }
        }
      }

      for (bc <- problem.negativeBlockingClauses) {
        dprintln("Lazy>-BC: " + bc)
        val blockingClause =
          (for ((s,t) <- bc) yield {
            if (teqt(s min t)(s max t) == -1)
              teqt(s min t)(s max t) =
                termEqTermAux(assignments(s), assignments(t))
            -teqt(s min t)(s max t)
          }).toArray

        try {
          negativeBlockingClauses += bc.toList
          solver.addClause(new VecInt(blockingClause))
          bcCount += 1
        } catch {
          case e : org.sat4j.specs.ContradictionException => {
            throw new Exception("Blocking Clauses are Contradictory")
          }
        }
      }      

      var iterations = 0
      // (1) Generate a random assignments A
      while (!infeasible && !allSat && solver.isSatisfiable()) {
        iterations += 1
        timeoutChecker()
        Timer.measure("LazySolver.assignmentsToSolution)") {
          candidate = assignmentsToSolution(assignments)
        }

        // (2) Check if A is a solution to the problem
        problem.testSolution(candidate) match {
          // (2a) if NO, go to (3)
          case Some(p) => {
            blockingProblem(p) = true
            // (3) Generate blocking clause B that excludes A
            // (4) Add B to the constraints and generate new assignment A'
            // (5) Let A = A' and go to (2)
            if (handleBlockingProblem(problem(p), candidate))
              infeasible = true
            problemOrder = p::problemOrder.filter(_ != p)
          }

          // (2b) if YES, terminate with A
          case None => allSat = true
        }
      }

      dprintln("LAZY>iterations: " + iterations)

      if (allSat) {
        S.addEntry("LAZY>RESULT:SAT,BLOCKINGCLAUSES:" + bcCount)
        (breu.Result.SAT, Some(candidate))
      } else {
        lastUnsatCore =
          (for (i <- 0 until problem.size; if (blockingProblem(i))) yield i)
        S.addEntry("LAZY>RESULT:UNSAT,BLOCKINGCLAUSES:" + bcCount)
        (breu.Result.UNSAT, None)
      }
    }

  override def getStat(result : breu.Result.Result) = 
    "LAZY>RESULT:" + result + ",BLOCKINGCLAUSES:" + bcCount

  def unsatCoreAux(problem : Problem, timeout : Int) = lastUnsatCore

  // def unitBlockingClauses = unitClauses
  // def blockingClauses = savedBlockingClauses

  // We automatically calculate unsatCore
  var lastUnsatCore = List() : Seq[Int]
  var unitClauses = ListBuffer() : ListBuffer[(Int, Int)]
  var bcCount = 0
}
