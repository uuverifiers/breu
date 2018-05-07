package breu;

import scala.collection.mutable.ListBuffer

/*
 * Helper class for constructing BREU-problems
 * 
 */
class BREUConstructor[Term, Fun]() {
  type Domain = (Term, Set[Term])
  type FunApp = (Fun, Seq[Term], Term)
  type Goal = Seq[(Term, Term)]

  val domains : ListBuffer[Domain] = ListBuffer()
  val functions : ListBuffer[ListBuffer[FunApp]] = ListBuffer()
  val negatedFunctions : ListBuffer[ListBuffer[FunApp]] = ListBuffer()
  val goals : ListBuffer[ListBuffer[Goal]] = ListBuffer()
  var subProblems = 0
  var tableColumns = List() : List[Int]
  var unitClauses = List() : List[(Int, Int)]
  var model = None : Option[Map[Int,Int]]

  def addDomain(t : Term, d : Set[Term]) =
    domains += ((t, d))

  def newSubproblem() = {
    subProblems += 1
    functions += ListBuffer()
    negatedFunctions += ListBuffer()
    goals += ListBuffer()
  }

  def addFunction(sp : Int, f : FunApp) =
    functions(sp) += f

  def addGoal(sp : Int, g : Goal) =
    goals(sp) += g

  def print() = {
    println("BREU CONSTRUCTOR")
    println("Subproblems: " + subProblems)
    println("Domains:")
    for ((t, d) <- domains) {
      println("\t" + t + " -> " + d.mkString(","))
    }

    for ((fs, gs) <- functions zip goals) {
      println("< --- SUBPROBLEM --- >")
      println("Functions:")
      for ((f, args, r) <- fs)
        println("\t" + f + "(" + args.mkString(",") + ") = " + r)
      println("Goals:")
      for (g <- gs)
        println("\t" + g)
    }
  }

  def checkTO() = {
  }

  private def solve(solver : breu.BREUSolver[Term,Fun]) = {
    // Create Problem
    val prob = solver.createProblem(
      domains.toMap,
      goals.toList,
      functions.toList,
      negatedFunctions.toList
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
