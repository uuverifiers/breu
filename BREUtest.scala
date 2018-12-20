object BREUtest {

  def checkTO() = {
  }

  def main(args : Array[String]) : Unit = {
    if (args.length < 1)
      return println("Usage: BREUtest input.breu [timeout]")
    val timeout : Long =
      if (args.length < 2)
        5000
      else
        args(1).toLong

    val cons = new breu.Constructor[String,String]()

    val input = io.Source.fromFile(args(0)).getLines.toList

    var section = ""

    val dPattern = "(.*)=(.*)".r
    val fPattern = "(.*)\\((.*)\\)=(.*)".r
    // val gPattern = "((.*)=\\?(.*)\\|?)+".r
    val gPattern = "(.*=\\?.*\\|?)+".r    

    for (l <- input) {
      l.trim() match {
        case dPattern(t,d) if section == "domains" => cons.addDomain(t, d.split(",").toSet)
        case fPattern(f,ts,t) if section == "problem" => cons.addFunction((f, ts.split(","), t))
        case gPattern(sgoals) => {
          println("GPATTERN: " + sgoals)
          val sgPattern = "(.*)=\\?(.*)".r
          val sgs = 
            for (sg <- sgoals.split("\\|")) yield {
              sg match {
                case sgPattern(lhs, rhs) => (lhs.toString, rhs.toString)
              }
            }
          cons.addGoal(sgs.toList)
        }
        case "DOMAINS" => section = "domains"
        case "PROBLEM" => {
          section = "problem"
          cons.newSubproblem()
        }
      }
    }

    println(cons)

    val t0 = System.nanoTime()
    val res = cons.solveLazy(timeout)
    val t1 = System.nanoTime()
    val runTime = t1 - t0
    res match {
      case breu.Result.SAT => {
        println("SAT")
        println("PositiveBlockingClauses: ")
        for (bc <- cons.posBlockingClauses)
          println("\t" + bc)
        println("NegativeBlockingClauses: ")
        for (bc <- cons.negBlockingClauses)
          println("\t" + bc)
      }
      case breu.Result.UNSAT => {
        println("UNSAT")
      }
      case breu.Result.UNKNOWN => {
        println("UNKNOWN")
      }
    }
    println("Time: " + runTime/1000000 + " ms")    
  }
}
