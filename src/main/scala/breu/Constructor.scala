package breu;

import scala.collection.mutable.ListBuffer

/*
 * Helper class for constructing BREU-problems
 * 
 */

class Constructor[Term, Fun]() {
  type Domain = (Term, Set[Term])
  type FunApp = (Fun, Seq[Term], Term)
  type Goal = Seq[(Term, Term)]

  val domains : ListBuffer[Domain] = ListBuffer()
  val eqs : ListBuffer[ListBuffer[FunApp]] = ListBuffer()
  val negatedEqs : ListBuffer[ListBuffer[FunApp]] = ListBuffer()

  val goals : ListBuffer[ListBuffer[Goal]] = ListBuffer()
  var subProblems = 0
  var tableColumns = List() : List[Int]
  var unitClauses = List() : List[(Int, Int)]
  var model = None : Option[Map[Int,Int]]

  def addDomain(t : Term, d : Set[Term]) =
    domains += ((t, d))

  def newSubproblem() = {
    subProblems += 1
    eqs += ListBuffer()
    negatedEqs += ListBuffer()
    goals += ListBuffer()
  }

  def addFunction(sp : Int, f : FunApp) =
    eqs(sp) += f

  def addGoal(sp : Int, g : Goal) =
    goals(sp) += g

  def print() : String = {
    " CONSTRUCTOR\n" +
    "Subproblems: " + subProblems + "\n" +
    "Domains:\n" +
    (for ((t, d) <- domains) yield {
      "\t" + t + " -> " + d.mkString(",")
    }).mkString("\n") +
    (for ((fs, gs) <- eqs zip goals) yield {
      "< --- SUBPROBLEM --- >\n" +
      "Eqs:\n" +
      (for ((f, args, r) <- fs) yield ("\t" + f + "(" + args.mkString(",") + ") = " + r)).mkString("\n") +
      "Goals:\n" +
      (for (g <- gs) yield ("\t" + g)).mkString("\n")
    }).mkString("\n")
  }

  def checkTO() = {}

  private def solve(solver : breu.Solver[Term,Fun]) = {
    // Create Problem
    val prob = solver.createProblem(
      domains.toMap,
      goals.toList,
      eqs.toList,
      negatedEqs.toList
    )

    // Solve Problem
    val res = prob.solve
    model = prob.model
    res
  }

  def solveTable(debug : Boolean = false) = {
    val solver = new breu.TableSolver[Term,Fun](checkTO, 60000)
    if (debug)
      solver.debug = true
    val ret = solve(solver)
    if (debug) {
      tableColumns = 
        (for (t <- solver.tables) yield {
          if (t.isDefined)
            t.get.currentColumn + 1
          else
            0
        }).toList
    }
    ret
  }

  def solveLazy(debug : Boolean = false) = {
    val solver = new breu.LazySolver[Term,Fun](checkTO, 60000)
    if (debug)
      solver.debug = true
    val ret = solve(solver)
    if (debug) {
      unitClauses = solver.unitBlockingClauses.toList
    }
    ret
  }  

}
