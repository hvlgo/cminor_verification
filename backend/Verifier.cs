/*
    TODO: 这是你唯一允许编辑的文件，你可以对此文件作任意的修改，只要整个项目可以正常地跑起来。
*/

using System.IO;
using System.Collections.Generic;

namespace cminor
{
    /// <summary> 一个验证器，接受一个中间表示，判断其是否有效。 </summary>
    class Verifier
    {
        SMTSolver solver = new SMTSolver();
        TextWriter writer;

        public Verifier(TextWriter writer)
        {
            this.writer = writer;
        }

        /// <summary> 应用此验证器 </summary>
        /// <param name="cfg"> 待验证的控制流图 </param>
        /// <returns> 验证结果 </returns>
        /// <list type="bullet">
        ///     <item> “&gt; 0” 表示所有的 specification 都成立 </item>
        ///     <item> “&lt; 0” 表示有一个 specification 不成立 </item>
        ///     <item> “= 0” 表示 unknown </item>
        /// </list>
        public Expression merge_expression(List<Expression> func)
        {
            Expression tmp;
            if (func.Count == 0)
            {
                tmp = new BoolConstantExpression(true);
            }
            else if (func.Count == 1)
            {
                tmp = func[0];
            }
            else
            {
                tmp = new AndExpression(func[0], func[1]);

                for (int j = 0; j < func.Count - 2; j++)
                {
                    tmp = new AndExpression(tmp, func[j + 2]);
                }
            }
            return tmp;
        }

        public Expression calculate_wlp_for_statement(Expression start, Statement currentStatement)
        {
            if (currentStatement is AssertStatement)
            {
                AssertStatement current = (AssertStatement)currentStatement;
                start = new AndExpression(start, current.pred);
            }
            else if (currentStatement is AssumeStatement)
            {
                AssumeStatement current = (AssumeStatement)currentStatement;
                start = new ImplicationExpression(current.condition, start);
            }
            else if (currentStatement is VariableAssignStatement)
            {
                VariableAssignStatement current = (VariableAssignStatement)currentStatement;
                start = start.Substitute(current.variable, current.rhs);
            }
            else if (currentStatement is SubscriptAssignStatement)
            {
                SubscriptAssignStatement current = (SubscriptAssignStatement)currentStatement;
                VariableExpression array = new VariableExpression(current.array);
                VariableExpression length = new VariableExpression(current.array.length);
                Expression tmp = new ArrayUpdateExpression(array, current.subscript, current.rhs, length); // there may have problems
                start = start.Substitute(current.array, tmp);
            }
            else if (currentStatement is FunctionCallStatement)
            {
                FunctionCallStatement current = (FunctionCallStatement)currentStatement;
                List<Expression> func = current.rhs.function.postconditionBlock.conditions;
                Expression tmp = merge_expression(func);
                if (current.rhs.argumentVariables.Count != current.rhs.function.parameters.Count)
                {
                    System.Console.WriteLine("the parameter length wrong");
                }
                for (int k = 0; k < current.rhs.argumentVariables.Count; k++)
                {
                    VariableExpression sub = new VariableExpression(current.rhs.argumentVariables[k]);
                    tmp = tmp.Substitute(current.rhs.function.parameters[k], sub);
                }
                if (current.lhs.Count != current.rhs.function.rvs.Count)
                {
                    System.Console.WriteLine("the return value length wrong");
                }
                for (int k = 0; k < current.lhs.Count; k++)
                {
                    VariableExpression sub = new VariableExpression(current.lhs[k]);
                    tmp = tmp.Substitute(current.rhs.function.rvs[k], sub);
                }
                start = new ImplicationExpression(tmp, start);
                List<Expression> pre = current.rhs.function.preconditionBlock.conditions;
                Expression tmp2 = merge_expression(pre);

                for (int k = 0; k < current.rhs.argumentVariables.Count; k++)
                {
                    VariableExpression sub = new VariableExpression(current.rhs.argumentVariables[k]);
                    tmp2 = tmp2.Substitute(current.rhs.function.parameters[k], sub);
                }
                start = new AndExpression(tmp2, start);
            }
            return start;
        }
        public Expression calculate_wlp_for_block(Expression start, Block currentBlock)
        {
            int num = currentBlock.statements.Count;
            LinkedListNode<Statement> nextStatementNode = currentBlock.statements.Last;
            for (int i = 0; i < num; i++)
            {
                LinkedListNode<Statement> currentStatementNode = nextStatementNode;
                Statement currentStatement = currentStatementNode.Value;
                nextStatementNode = currentStatementNode.Previous;
                start = calculate_wlp_for_statement(start, currentStatement);
                
            }
            return start;
        }

        public Expression calculate_wlp_for_path(LinkedList<Block> path, Expression start)
        {
            int times = path.Count;
            for (int i = 0; i < times - 1; i++)
            {
                Block currentBlock = path.Last.Value;
                start = calculate_wlp_for_block(start, currentBlock);
                path.RemoveLast();
            }
            Block final = path.Last.Value;
            if (final is LoopHeadBlock)
            {
                LoopHeadBlock loop = (LoopHeadBlock)final;
                start = calculate_wlp_for_block(start, loop);
                Expression tmp = merge_expression(loop.invariants);
                start = new ImplicationExpression(tmp, start);
            }
            else if (final is PreconditionBlock)
            {
                PreconditionBlock pre = (PreconditionBlock)final;
                Expression tmp = merge_expression(pre.conditions);
                start = new ImplicationExpression(tmp, start);
            }
            else
            {
                System.Console.WriteLine("end at a strange block");
            }
            return start;
        }
        public bool verifier_basic_path(LinkedList<Block> past)
        {
            LinkedList<Block> path = new LinkedList<Block>(past);
            Block end = path.Last.Value;
            Expression start;
            path.RemoveLast();
            if (end is PostconditionBlock)
            {
                PostconditionBlock post = (PostconditionBlock)end;
                start = merge_expression(post.conditions);
            }
            else
            {
                LoopHeadBlock loop = (LoopHeadBlock)end;
                start = merge_expression(loop.invariants);
            }
            start = calculate_wlp_for_path(path, start);

            bool result = (solver.CheckValid(start) == null);
            return result;
        }

        public (int, LinkedList<Block>, List<Expression>, List<Expression>) get_position(LinkedList<Block> path)
        {
            List<Expression> rank = default!;
            List<Expression> before = default!;
            while (true)
            {
                path.RemoveLast();
                if (path.Count == 1)
                {

                    return (-2, path, rank, before); // -2 代表这个基本路径中没有找到 function_call
                }
                Block currentBlock = path.Last.Value;
                int num = currentBlock.statements.Count;
                LinkedListNode<Statement> nextStatementNode = currentBlock.statements.Last;
                for (int i = 0; i < num; i++)
                {
                    LinkedListNode<Statement> currentStatementNode = nextStatementNode;
                    Statement currentStatement = currentStatementNode.Value;
                    nextStatementNode = currentStatementNode.Previous;
                    if (currentStatement is FunctionCallStatement)
                    {
                        FunctionCallStatement current = (FunctionCallStatement)currentStatement;
                        rank = new List<Expression> (current.rhs.function.preconditionBlock.rankingFunctions);
                        for (int k = 0; k < current.rhs.argumentVariables.Count; k++)
                        {
                            VariableExpression sub = new VariableExpression(current.rhs.argumentVariables[k]);
                            int c = rank.Count;
                            for (int m = 0; m < c; m++)
                            {
                                rank[m] = rank[m].Substitute(current.rhs.function.parameters[k], sub);
                            }
                        }
                        before = current.rhs.function.preconditionBlock.conditions;
                        return (i, path, rank, before);
                    }
                    else
                    {
                        continue;
                    }
                }
            }
        }
        public (int, LinkedList<Block>, List<Expression>, List<Expression>) get_start_position(int pos, LinkedList<Block> path)
        {
            Block end = path.Last.Value;
            List<Expression> rank = default!;
            List<Expression> before = default!;

            if (pos == -1)
            {
                if (end is PostconditionBlock)
                {
                    return get_position(path);
                }
                else if (end is LoopHeadBlock)
                {
                    LoopHeadBlock loop = (LoopHeadBlock)end;
                    rank = loop.rankingFunctions;
                    before = loop.invariants;
                    pos = -3; // -3 代表这是 Loop 产生的链，需要对每一个statement计算wlp
                    path.RemoveLast();
                    return (pos, path, rank, before);
                }
                else
                {
                    System.Console.WriteLine("end at strange block");
                }
            }
            else if (pos >= 0 || pos == -3)
            {
                if (end is BasicBlock)
                {
                    BasicBlock currentBlock = (BasicBlock)end;
                    int num = currentBlock.statements.Count;
                    LinkedListNode<Statement> nextStatementNode = currentBlock.statements.Last;
                    for (int i = 0; i < num; i++)
                    {
                        LinkedListNode<Statement> currentStatementNode = nextStatementNode;
                        Statement currentStatement = currentStatementNode.Value;
                        nextStatementNode = currentStatementNode.Previous;
                        if (i <= pos)
                        {
                            continue;
                        }
                        if (currentStatement is FunctionCallStatement)
                        {
                            FunctionCallStatement current = (FunctionCallStatement)currentStatement;
                            rank = new List<Expression> (current.rhs.function.preconditionBlock.rankingFunctions);
                            if (current.rhs.argumentVariables.Count != current.rhs.function.parameters.Count)
                            {
                                System.Console.WriteLine("the parameter length wrong");
                            }
                            for (int k = 0; k < current.rhs.argumentVariables.Count; k++)
                            {
                                VariableExpression sub = new VariableExpression(current.rhs.argumentVariables[k]);
                                int c = rank.Count;
                                for (int m = 0; m < c; m++)
                                {
                                    rank[m] = rank[m].Substitute(current.rhs.function.parameters[k], sub);
                                }
                            }
                            before = current.rhs.function.preconditionBlock.conditions;
                            return (i, path, rank, before); // i 代表最后一个块的前 i 个statement 不需要计算 wlp
                        }
                    }
                    return get_position(path);
                }
                else if (end is PreconditionBlock)
                {
                    return (-2, path, rank, before);
                }
                
            }
            else
            {
                System.Console.WriteLine("value of pos is wrong");
            }
            
            return (pos, path, rank, before);
        }
        public bool rank_verifier_basic_path_from_statement(int pos, LinkedList<Block> past, List<Expression>r)
        {
            List<Expression> rank = new List<Expression>(r);
            LinkedList<Block> path = new LinkedList<Block>(past);
            Block first = path.First.Value;
            List<Expression> pre = default!;
            if (first is LoopHeadBlock)
            {
                LoopHeadBlock loop = (LoopHeadBlock)first;
                pre = new List<Expression>(loop.rankingFunctions);

            }
            else
            {
                PreconditionBlock p = (PreconditionBlock)first;
                pre = new List<Expression> (p.rankingFunctions);
            }
            
            HashSet<LocalVariable> visited = new HashSet<LocalVariable>();
            HashSet<LocalVariable> new_visited = new HashSet<LocalVariable>();
            foreach (Expression e in pre)
            {
                visited.UnionWith(e.GetFreeVariables());
            }
            Dictionary<LocalVariable, LocalVariable> r_map = new Dictionary<LocalVariable, LocalVariable>();
            Dictionary<LocalVariable, LocalVariable> map = new Dictionary<LocalVariable, LocalVariable>();

            foreach (LocalVariable e in visited)
            {
                LocalVariable new_e = new LocalVariable();
                new_e.name = "new" + e.name;
                new_e.type = e.type;
                new_visited.Add(new_e);
                map.Add(e, new_e);
                r_map.Add(new_e, e);
            }
            int num = pre.Count;
            for (int i = 0; i < num; i++)
            {
                foreach (LocalVariable v in visited)
                {
                    VariableExpression e = new VariableExpression(map[v]);
                    pre[i] = pre[i].Substitute(v, e);
                }
            }
            Expression start = new BoolConstantExpression(false);
            for (int i = 0; i < num; i++)
            {
                Expression tmp = new BoolConstantExpression(true);
                for (int j = 0; j < i; j++)
                {
                    EQExpression eq = new EQExpression(rank[j], pre[j]);
                    tmp = new AndExpression(tmp, eq);
                }
                LTExpression lt = new LTExpression(rank[i], pre[i]);
                tmp = new AndExpression (tmp, lt);
                start = new OrExpression(start, tmp);
            }
            start.Print(this.writer);
            System.Console.WriteLine();
            if (pos == -3)
            {
                start = calculate_wlp_for_path(path, start);
            }
            else 
            {
                Block currentBlock = path.Last.Value;
                int n = currentBlock.statements.Count;
                LinkedListNode<Statement> nextStatementNode = currentBlock.statements.Last;
                for (int i = 0; i < n; i++)
                {
                    LinkedListNode<Statement> currentStatementNode = nextStatementNode;
                    Statement currentStatement = currentStatementNode.Value;
                    nextStatementNode = currentStatementNode.Previous;
                    if (i <= pos)
                    {
                        continue;
                    }
                    start = calculate_wlp_for_statement(start, currentStatement);
                }
                path.RemoveLast();
                start = calculate_wlp_for_path(path, start);
            }

            start.Print(this.writer);
            System.Console.WriteLine();
            foreach (LocalVariable v in new_visited)
            {
                VariableExpression e = new VariableExpression(r_map[v]);
                start = start.Substitute(v, e);
            }
            start.Print(this.writer);
            System.Console.WriteLine();
            
            bool result = (solver.CheckValid(start) == null);
            return result;
        }
        public bool rank_verifier_basic_path(LinkedList<Block> path)
        {
            int startPosOfStatement = -1;
            List<Expression> rank;
            List<Expression> before;
            while (true)
            {
                (startPosOfStatement, path, rank, before) = get_start_position(startPosOfStatement, path);
                if (startPosOfStatement == -2)
                {
                    return true;
                }
                bool result = rank_verifier_basic_path_from_statement(startPosOfStatement, path, rank);
                if (!result)
                {
                    return false;
                }
            }
        }
        public int Apply(IRMain cfg)
        {
            foreach (Predicate p in cfg.predicates)
            {
                solver.definePredicate(p);
            }
            bool need_judge_rank = false;
            if (cfg.functions.Count == 0)
            {
                return 1;
            }
            else
            {
                need_judge_rank = (cfg.functions.First.Value.preconditionBlock.rankingFunctions.Count > 0);
            }
            while (cfg.functions.Count > 0)
            {
                HashSet<string> visited = new HashSet<string>();

                Function f = cfg.functions.First.Value;


                if (need_judge_rank)
                {
                    IntConstantExpression zero = new IntConstantExpression(0);
                    List<Expression> geList = new List<Expression>();
                    for (int n = 0; n < f.preconditionBlock.rankingFunctions.Count; n++)
                    {
                        GEExpression ge = new GEExpression(f.preconditionBlock.rankingFunctions[n], zero);
                        geList.Add(ge);
                    }
                    Expression allge = merge_expression(geList);
                    ImplicationExpression nonneg = new ImplicationExpression(merge_expression(f.preconditionBlock.conditions), allge);
                    bool res = (solver.CheckValid(nonneg) == null);
                    if (!res)
                    {
                        return -1;
                    }
                }
                
                Queue<Block> node = new Queue<Block>();
                Queue<LinkedList<Block>> paths = new Queue<LinkedList<Block>>();
                node.Enqueue(f.preconditionBlock);
                LinkedList<Block> path = new LinkedList<Block>();
                path.AddLast(f.preconditionBlock);
                paths.Enqueue(path);
                while (node.Count > 0)
                {
                    Block currentBlock = node.Dequeue();
                    LinkedList<Block> currentPath = paths.Dequeue();
                    if (currentBlock is LoopHeadBlock || currentBlock is PostconditionBlock)
                    {
                        foreach (Block block in currentPath)
                        {
                            System.Console.Write(block.ToString() + "->");
                        }
                        System.Console.WriteLine();
                        bool result = verifier_basic_path(currentPath);
                        if (!result)
                        {
                            return -1;
                        }
                        
                        if (need_judge_rank)
                        {
                            if (currentBlock is LoopHeadBlock)
                            {
                                LoopHeadBlock tmp = (LoopHeadBlock)currentBlock;
                                IntConstantExpression zero = new IntConstantExpression(0);
                                List<Expression> geList = new List<Expression>();
                                for (int n = 0; n < tmp.rankingFunctions.Count; n++)
                                {
                                    GEExpression ge = new GEExpression(tmp.rankingFunctions[n], zero);
                                    geList.Add(ge);
                                }
                                Expression allge = merge_expression(geList);
                                ImplicationExpression nonneg = new ImplicationExpression(merge_expression(tmp.invariants), allge);
                                bool res = (solver.CheckValid(nonneg) == null);
                                if (!res)
                                {
                                    return -1;
                                }
                            }
                            bool rank_result = rank_verifier_basic_path(currentPath);
                            if (!rank_result)
                            {
                                return -1;
                            }
                        }
                        if (!visited.Contains(currentBlock.ToString()))
                        {
                            foreach (Block son in currentBlock.successors)
                            {
                                node.Enqueue(son);
                                LinkedList<Block> newPath = new LinkedList<Block>();
                                newPath.AddLast(currentBlock);
                                newPath.AddLast(son);
                                paths.Enqueue(newPath);
                            }
                        }
                        visited.Add(currentBlock.ToString());

                    }
                    else
                    {
                        foreach (Block son in currentBlock.successors)
                        {
                            node.Enqueue(son);
                            LinkedList<Block> newPath = new LinkedList<Block>();
                            foreach (Block block in currentPath)
                            {
                                newPath.AddLast(block);
                            }
                            newPath.AddLast(son);
                            paths.Enqueue(newPath);
                        }
                    }
                }
                cfg.functions.RemoveFirst();
            }
            return 1;
        }

    }
}