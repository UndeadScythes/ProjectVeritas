<?php
    abstract class Type {
        const P = "predicate"; // P(a,b,c) -| formula
        const O = "operator";  // a * b -| formula
        const F = "function";  // a * b = object
        const L = "logic";     // a * b ...
    }
    
    abstract class Symbol {
        const a = "small";
        const A = "big";
        const s = "symbol";
        const F = "formula";
        const aa = "array";
    }

    class T {
        public static $db;
        public static $i = array(
            Symbol::a => 0,
            Symbol::A => 0,
            Symbol::s => 0,
            Symbol::F => 0
        );
        public static $symbols = array(
            Symbol::a => "abcde",
            Symbol::A => "ABCDE",
            Symbol::s => array("\ast", "\diamond"),
            Symbol::F => array("\Phi", "\Psi")
        );
        public static $terms = array();
        public static $expand = array();
        
        public $type;
        public $title;
        public $name;
        public $quick;
        public $display;
        public $init;
        
        function __construct($type, $title, $name, $quick, $display, $init) {
            $this->type = $type;
            $this->title = $title;
            $this->name = $name;
            $this->quick = $quick;
            $this->display = $display;
            $this->init = $init;
            self::$db[$this->name] = $this;
        }
        
        public function introduce() {
            $array = self::make($this->init);
            $quick = $this->quick;
            $display = $this->display;
            switch ($this->type) {
                case Type::P:
                    return $quick($array) . " \dashv " . $display($array);
                case Type::O:
                case Type::L:
                    return $quick($array[0], $array[1]) . " \dashv " . $display($array[0], $array[1]);
                default:
                    return "\mathsf{ $this->name}^?";
            }
        }
        
        public function simple() {
            $array = self::make($this->init);
            $quick = $this->quick;
            switch ($this->type) {
                case Type::P:
                    return $quick($array);
                case Type::O:
                case Type::L:
                    return $quick($array[0], $array[1]);
                default:
                    return "\mathsf{ $this->name}^?";
            }
        }
        
        public function complex() {
            $array = self::make($this->init);
            $display = $this->display;
            switch ($this->type) {
                case Type::P:
                    return $display($array);
                case Type::O:
                case Type::L:
                    return $display($array[0], $array[1]);
                default:
                    return "\mathsf{ $this->name}^?";
            }
        }
        
        public static function resetVars() {
            foreach (self::$i as $k => $v) {
                self::$i[$k] = 0;
            }
        }
        
        public static function make($init) {
            $array = array();
            foreach($init as $var) {
                $array[] = self::getNext($var);
            }
            return $array;
        }
        
        public static function getNext($var) {
            if ($var == Symbol::aa) {
                return array(self::getNext(Symbol::a));
            } else {
                $symbol = self::$symbols[$var][self::$i[$var]];
                self::$i[$var]++;
                return $symbol;
            }
        }
        
        public static function o($a, $op, $b) {
            self::$terms[] = $op;
            $truth = self::getTruth($op);
            if (self::expanded($op)) {
                $display = $truth->display;
                return "\left(" . $display($a, $b) . "\\right)";
            } else {
                $quick = $truth->quick;
                return $quick($a, $b);
            }
        }
        
        public static function expanded($name) {
            return in_array($name, self::$expand);
        }
        
        public static function f($op, $array) {
            self::$terms[] = $op;
            $truth = self::getTruth($op);
            if ($truth->type == Type::L) {
                $quick = $truth->quick;
                return $quick("$truth->name^?", "\{" . join(",", $array) . "\}");
            } else if (self::expanded($op)) {
                $display = $truth->display;
                return $display($array);
            } else {
                $quick = $truth->quick;
                return $quick($array);
            }
        }
        
        public static function pred($name, $array) {
            return "\underset{\mathsf{" . strtoupper($name) . "}}{\underline{P\left(" . join(",", $array) . "\\right)}}";
        }
        
        public static function getTruth($name) {
            if (array_key_exists($name, self::$db)) {
                return self::$db[$name];
            } else {
                return new T(Type::L, "Unknown operator ($name)", "$name",
                        function($a,$b) {return "$a \operatorname{?} $b";},
                        function($a,$b) {return "$a \operatorname{?} $b";},
                        array(Symbol::A, Symbol::A));
            }
        }
    }
    
    new T(Type::O, "Set membership", "in",
            function($a,$b) {return "$a \in $b";},
            function($a,$b) {return T::pred("member", array($a, $b));},
            array(Symbol::a, Symbol::A));
    new T(Type::O, "Subset", "subseteq",
            function($a,$b) {return "$a \subseteq $b";},
            function($a,$b) {
                $c = T::getNext(Symbol::a);
                return T::o(T::o($c, "in", $a), "implies", T::o($c, "in", $b));
            },
            array(Symbol::A, Symbol::A));
    new T(Type::O, "Material conditional", "implies",
            function($a,$b) {return "$a \\rightarrow $b";},
            function($a,$b) {return T::f("neg", array("\left(" . T::o($a, "and", T::f("neg", array($b))) . "\\right)"));},
            array(Symbol::A, Symbol::A));
    new T(Type::L, "Negation", "neg",
            function($a) {return "\\neg $a[0]";},
            function($a) {return "\\neg $a[0]";},
            array(Symbol::A));
    new T(Type::L, "Conjunction", "and",
            function($a,$b) {return "$a \wedge $b";},
            function($a,$b) {return "$a \wedge $b";},
            array(Symbol::A, Symbol::A));
    new T(Type::O, "Set equality", "equal",
            function($a,$b) {return "$a = $b";},
            function($a,$b) {return T::o(T::o($a, "subseteq", $b), "and", T::o($b, "subseteq", $b));},
            array(Symbol::A, Symbol::A));
    new T(Type::P, "Universal quantifier", "forall",
            function($a) {return "\\forall " . T::o(join(",",$a[0]), "in", $a[1]) . "\left[$a[2]\\right]";},
            function($a) {
                $ins = array();
                foreach ($a[0] as $b) {
                    array_push($ins, T::o($b, "in", $a[1]));
                }
                $ands = $ins[0];
                for ($i = 1; $i < count($ins); $i++) {
                    $ands = T::o($ands, "and", $ins[$i]);
                }
                $result = "";
                foreach ($a[0] as $b) {
                    $result .= "\\forall $b";
                }
                return $result . T::o("\left[\left($ands\\right)", "implies", "$a[2]\\right]");
            },
            array(Symbol::aa, Symbol::A, Symbol::F));
    new T(Type::P, "Associativity", "assoc",
            function($a) {return T::pred("assoc", $a);},
            function($a) {
                $c = T::getNext(Symbol::a);
                $d = T::getNext(Symbol::a);
                $e = T::getNext(Symbol::a);
                return T::o(T::f("binop", $a), "and", T::f("forall", array(array($c, $d, $e), $a[0], T::o("\left($c $a[1] $d\\right) $a[1] $e", "equal", "$c $a[1] \left($d $a[1] $e\\right)"))));
            },
            array(Symbol::A, Symbol::s));

    $topic = filter_input(INPUT_GET, "topic");
    T::$expand = explode(",", filter_input(INPUT_GET, "expand"));
?>
<!DOCTYPE html>
<html>
    <head>
        <meta charset="UTF-8">
        <title>Project Veritas</title>
        <script type="text/x-mathjax-config">
            MathJax.Hub.Config({tex2jax: {inlineMath: [['$','$'], ['\\(','\\)']]}});
        </script>
        <script
            type="text/javascript"
            src="https://cdn.mathjax.org/mathjax/latest/MathJax.js?config=TeX-AMS-MML_HTMLorMML">
        </script>
    </head>
    <body>
        <h1>Project Veritas</h1>
        <?php
            if ($topic == "") {
                $title = "Glossary";
                foreach (T::$db as $truth) {
                    if ($truth->type != Type::L) {
                        T::$terms[] = $truth->name;
                    }
                }
                $display = "$ P(\mathsf{roject})\sim V^2\!\mathrm{eritas}$";
            } else {
                $display = "$" . T::getTruth($topic)->introduce() . "$";
            }
        ?>
        <h2><?=$title?></h2>
        <p><?=$display?></p>
        <ul>
            <?php
                    $terms = array_unique(T::$terms);
                    foreach ($terms as $term) {
                        T::resetVars();
                        $truth = T::getTruth($term);
                        $note = $truth->title . ": $" . $truth->simple() . "$";
                        echo "<li>$note";
                        if ($truth->type != Type::L) {
                            echo " <a href='?topic=$term'>link</a>";
                            if (T::expanded($term)) {
                                $arr = [];
                                foreach (T::$expand as $item) {
                                    if ($item != $term) {
                                        $arr[] = $item;
                                    }
                                }
                                $newArr = join(",", $arr);
                                echo " <a href='?topic=$topic&expand=$newArr'>contract</a>";
                            } else {
                                $newArr = join(",", T::$expand) . ",$term";
                                echo " <a href='?topic=$topic&expand=$newArr'>expand</a>";
                            }
                        }
                        echo "</li>";
                    }
            ?>
            <li><a href='?topic=<?=$topic?>'>reset</a></li>
            <li><a href='?topic='>glossary</a></li>
        </ul>
    </body>
</html>
