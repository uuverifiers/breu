package breu;

object Tester {
  def test(file : String, timeout : Long) : breu.Result.Value = {
    // TODO: How many bits?
    val solver = new breu.Solver[String, String](8)

    val input = io.Source.fromFile(file).getLines.toList
    var problem = 0

    val gPattern = "(.*=\\?.*\\|?)+".r
    val fPattern = "(.*)\\((.*)\\)=(.*)".r    
    val dPattern = "(.*)=(.*)".r    

    for (l <- input) {
      l.trim() match {
        case gPattern(sgoals) => {
          val sgPattern = "(.*)=\\?(.*)".r
          val sgs = 
            for (sg <- sgoals.split("\\|")) yield {
              sg match {
                case sgPattern(lhs, rhs) => (lhs.toString, rhs.toString)
              }
            }
          solver.addGoal(sgs.toList)
        }        

        case fPattern(f,"",t) => {
          solver.addFunction((f, List(), t))
        }

        case fPattern(f,ts,t) => {
          solver.addFunction((f, ts.split(","), t))
        }          

        case dPattern(t,d) => {
          solver.addVariable(t, d.split(",").toSet)
        }          

        case "PROBLEM" => {
          if (problem > 0)
            solver.push()
          problem += 1
        }
        case "DOMAINS" => {}
      }
    }

    solver.push()
    try {
      solver.solve(timeout)
    } catch {
      case te : TimeoutException =>{
        breu.Result.UNKNOWN
      }
    }
  }  
}
