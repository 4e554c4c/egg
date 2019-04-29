use std::fmt;

use crate::egraph::EGraph;

pub struct Dot<'a> {
    egraph: &'a EGraph,
}

impl<'a> Dot<'a> {
    pub fn new(egraph: &EGraph) -> Dot {
        Dot { egraph }
    }
}

impl<'a> fmt::Display for Dot<'a> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        write!(f, "digraph {{\n")?;

        // set compound=true to enable edges to clusters
        write!(f, "  compound=true\n")?;

        // define all the nodes, clustered by eclass
        for (leader, class) in &self.egraph.classes {
            write!(f, "  subgraph cluster_{} {{\n", leader.0)?;
            write!(f, "    style=dotted\n")?;
            for (i, node) in class.iter().enumerate() {
                write!(f, "    {}.{}[label = \"", leader.0, i)?;
                node.write_label(f)?;
                write!(f, "\"]\n")?;
            }
            write!(f, "  }}\n")?;
        }

        for (leader, class) in &self.egraph.classes {
            for (i_in_class, node) in class.iter().enumerate() {
                for (arg_i, child) in node.children().iter().enumerate() {
                    // write the edge to the child, but clip it to the eclass with lhead
                    let child_leader = self.egraph.leaders.just_find(child.0);
                    write!(
                        f,
                        // {}.0 to pick an arbitrary node in the cluster
                        "  {}.{} -> {}.0 [lhead = cluster_{}, label = {}]\n",
                        leader.0, i_in_class, child.0, child_leader, arg_i
                    )?;
                }
            }
        }

        write!(f, "}}")
    }
}