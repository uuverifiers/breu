package breu;

import scala.collection.mutable.ListBuffer

class BREUConstructor[Term, Fun]() {
  type Domain = (Term, Set[Term])
  type FunApp = (Fun, Seq[Term], Term)
  type Goal = Seq[(Term, Term)]

  val domains : ListBuffer[Domain] = ListBuffer()
  val functions : ListBuffer[ListBuffer[FunApp]] = ListBuffer()
  val negatedFunctions : ListBuffer[ListBuffer[FunApp]] = ListBuffer()
  val globalFunctions : ListBuffer[FunApp] = ListBuffer()
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

  def addGlobalFunction(f : FunApp) =
    globalFunctions += f

  def addFunction(f : FunApp) =
    functions.last += f

  def addGoal(g : Goal) =
    goals.last += g

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


  // FlatZinc Code

  def genNoCongPairs(p : Int) = {
    val funSymbols = (globalFunctions ++ functions(p)).toList.map(_._1).toSet
    val congPairs = 
      (for (fs <- funSymbols) yield {
        val funApps = (globalFunctions ++ functions(p)).toList.filter(_._1 == fs)
        for (i <- 0 until funApps.length; j <- 0 until funApps.length; if (i != j)) yield {
          1
        }
      }).flatten

    congPairs.sum
  }


  def genCongPairs(p : Int, tm : Map[Term, Int]) : List[List[Int]] = {
    val maxArgs = (globalFunctions ++ functions.flatten).toList.maxBy(_._2.length)._2.length
    val funSymbols = (globalFunctions ++ functions(p)).toList.map(_._1).toSet

    (for (fs <- funSymbols) yield {
      val funApps = (globalFunctions ++ functions(p)).toList.filter(_._1 == fs)
      (for (i <- 0 until funApps.length; j <- 0 until funApps.length; if (i != j)) yield {
        val (_, a1, b1) = funApps(i)
        val (_, a2, b2) = funApps(j)
        val pad = List.fill(maxArgs - a1.length)(0)
        pad ++ a1.map(tm(_)) ++ List(tm(b1)) ++ pad ++ a2.map(tm(_)) ++ List(tm(b2))
      }).toList
    }).toList.flatten
  }

  def genGoals(p : Int, goalCount : Int, goalLength : Int, tm : Map[Term, Int]) = {
    val emptyGoal = List.fill(goalLength*2)(0).mkString(",")
    // val paddedGoals = goals(p) ++ List.fill(goalCount - goals(p).length)(emptyGoal)
    val gs = 
      (for (g <- goals(p)) yield {
        val lhs = g.map(_._1).map(tm(_))
        val rhs = g.map(_._2).map(tm(_))
        val pad = List.fill(goalLength - g.length)(0)
        val res = (lhs ++ pad ++ rhs ++ pad)
        res.mkString(",")
      }) ++ List.fill(goalCount - goals(p).length)(emptyGoal)

    gs.mkString(",")
  }

  def toDZN() : String = {
    val sortedDomains = domains.toList
    val termMap = (sortedDomains.map(_._1) zip sortedDomains.indices.map(_ + 1)).toMap

    val argsLength = (for (p <- 0 until subProblems) yield ((globalFunctions ++ functions(p)).map(_._2.length).max)).mkString("[",",","]")
    val congPairs = for (p <- 0 until subProblems) yield genCongPairs(p, termMap)
    val maxCongPairs = congPairs.map(_.length).max
    val maxArgs = (globalFunctions ++ functions.flatten).toList.maxBy(_._2.length)._2.length
    val emptyCongPair = List.fill(maxArgs*2+2)(0)
    val paddedCongPairs = for (p <- 0 until subProblems) yield {
      congPairs(p) ++ List.fill(maxCongPairs - congPairs(p).length)(emptyCongPair)
    }

    val noCongPairs = for (p <- 0 until subProblems) yield congPairs(p).length
    val tableCols = tableColumns.map(x => if (x == 0) tableColumns.max else x).mkString("[",",","]")
    val goalsCount = goals.map(_.length).max
    val goalsLength = goals.flatten.map(_.length).max
    val goalsStr = (for (p <- 0 until subProblems) yield genGoals(p, goalsCount, goalsLength, termMap)).mkString("[|", "|", "|]")

    // for ((k,v) <- termMap)
    //   println("% " + k + " -> " + v)

    val intDomains =
      "[" + (for ((t, ts) <- sortedDomains) yield {
        "{" + ts.map(termMap(_)).mkString(",") + "}"
      }).mkString(",\n") + "]"

    val str = 
      "noProblems = " + subProblems + ";\n" +
    "noSymbols = " + domains.length + ";\n" +
    "noColumns = " + tableCols + ";\n" + 
    "noCongPairs = " + noCongPairs.mkString("[",",","]") + ";\n" +
    "argsLength = " + argsLength + ";\n" +
    "\n" +
    "Domains =\n" +
    intDomains + ";\n" +
    "CongruencePairs = \n" + paddedCongPairs.map(x => x.map(_.mkString(",")).mkString(",\n")).mkString("[|","|","|]") + ";\n" +
    "noGoals = " + goals.map(_.length).mkString("[",",","]") + ";\n" +
    "goalsLength = " + goals.map(x => x.map(y => y.length).max).mkString("[",",","]") + ";\n" +
    "Goals = \n" +
    goalsStr + ";\n"
    str
  }

  private def solve(solver : breu.BREUSolver[Term,Fun]) = {
    // Create Problem
    val prob = solver.createProblem(
      domains.toMap,
      goals.toList,
      functions.toList.map(_ ++ globalFunctions.toList),
      negatedFunctions.toList
    )

    // Solve Problem
    val res = prob.solve

    println(res)

    model = prob.model
  }



  def solveTable(debug : Boolean = false) = {
    val solver = new breu.TableSolver[Term,Fun](checkTO, 60000)
    if (debug)
      solver.debug = true
    solve(solver)
    if (debug) {
      tableColumns = 
        (for (t <- solver.tables) yield {
          if (t.isDefined)
            t.get.currentColumn + 1
          else
            0
        }).toList
    }
  }

  def solveLazy(debug : Boolean = false) = {
    val solver = new breu.LazySolver[Term,Fun](checkTO, 60000)
    if (debug)
      solver.debug = true
    solve(solver)
    if (debug) {
      unitClauses = solver.unitBlockingClauses.toList
    }
  }  

}
