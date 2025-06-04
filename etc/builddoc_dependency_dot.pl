print "digraph depend {\n";
print "  node [shape = ellipse,style=filled,colorscheme = paired12];\n";
print "  subgraph cluster_analysis { label=\"Analysis\" }\n";
print "  subgraph cluster_classical { label=\"Classical\" }\n";
print "  subgraph cluster_reals { label=\"Reals\" }\n";
print "  subgraph cluster_experimental_reals { label=\"ExperimentalReals\" }\n";
print "  subgraph cluster_analysis { label=\"Analysis\" }\n";
print "  subgraph cluster_topology { label=\"Topology\" }\n";
print "  subgraph cluster_normedtype { label=\"NormedType\" }\n";
print "  subgraph cluster_lebesgue_integral { label=\"Lebesgue_integral\" }\n";
while (<>) {
  if (m/([^\s]*)\.vo.*:(.*)/) {
    $dests = $2 ;
    ($path,$src) = ($1 =~ s/\//\//rg =~ m/^(?:(.*\/))?([^.]*)$/);
    if ($path =~ m/classical\//) {
        $url="mathcomp.classical.$src.html";
        print "subgraph cluster_classical { \"$path$src\"[label=\"$src\",URL=\"$url\",fillcolor=1]}\n";
    }elsif ($path =~ m/reals\// or $path =~ m/reals_stdlib\//) {
        print "subgraph cluster_reals { \"$path$src\"[label=\"$src\",fillcolor=2,fontcolor=white]}"
    }elsif ($path =~ m/experimental_reals\//) {
        print "subgraph cluster_experimental_reals { \"$path$src\"[label=\"$src\",fillcolor=3]}"
    }elsif ($path =~ m/theories\/topology_theory\//) {
        print "subgraph cluster_topology { \"$path$src\"[label=\"$src\",fillcolor=4,fontcolor=white]}"
    }elsif ($path =~ m/theories\/normedtype_theory\//) {
        print "subgraph cluster_normedtype { \"$path$src\"[label=\"$src\",fillcolor=9]}"
    }elsif ($path =~ m/theories\/lebesgue_integral_theory\//) {
        print "subgraph cluster_lebesgue_integral { \"$path$src\"[label=\"$src\",fillcolor=10,fontcolor=white]}"
    }elsif ($path =~ m/theories\//) {
       print "subgraph cluster_analysis { \"$path$src\"[label=\"$src\",fillcolor=5]}"
    }elsif ($path =~ m/analysis_stdlib\/.*/) {
       print "subgraph cluster_analysis { \"$path$src\"[label=\"$src\",fillcolor=5]}"
    }else {
        $url="/mathcomp.$src.html";
        print "\"$path$src\"[label=\"$src\",URL=\"$url\",fillcolor=6,fontcolor=white]"
    }
    for my $dest (split(" ", $dests)) {
        print "  \"$1\" -> \"$path$src\";\n" if ($dest =~ m/(.*)\.vo/);
    }
  }
}
print "}\n";
