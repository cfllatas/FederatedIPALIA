using com.espertech.esper.compat.collections;
using pm4h.algorithm.i2palia;
using pm4h.algorithm.palia.Core;
using pm4h.algorithm.palia.Core.ipalia;
using pm4h.algorithm.palia.Core.palia2;
using pm4h.common;
using pm4h.data;
using pm4h.tpa;
using pm4h.tpa.ipi;
using pm4h.utils;
using pm4h.utils.saver;
using Sabien.Core3.Utils.core2.Maths;
using Sabien.Utils;
using System;
using System.Collections.Generic;
using System.Diagnostics;
using System.IO;
using System.Linq;
using System.Text;
using System.Threading.Tasks;

namespace pm4h.IPALIA
{
    public class I2PaliaFederated : IPMAppVerbosityAlgorithm
    {
        protected SharedLog parentsl;

        protected SharedLog sl;

        public i2TPA BaseTPA { get; set; }

        public static bool AuditCorrection = true;

        public TransitionsMergeMode MergingPolicy { get; set; } = TransitionsMergeMode.Equivalent;


        public ParallelMode ParalelismPolicy { get; set; } = ParallelMode.No;


        public SyncRegionMode SyncRegionPolicy { get; set; }

        public ParallelIdentificationMode ParallelIdentificationPolicy { get; set; }

        public void SetParentLog(SharedLog _sl)
        {
            parentsl = _sl;
        }

        public TPATemplate DiscoveryModel2(IPMLog log)
        {
            return DiscoveryModel(log).ToTPATemplate();
        }

        public TPATemplate SimpleAcceptorTree(IPMLog log)
        {
            SharedLog sharedLog = new SharedLog("Aceptor Tree", log.Count(), sl);
            TPATemplate tPATemplate = new TPATemplate2();
            foreach (PMTrace item in log.IterateTraces())
            {
                sharedLog.NewEvent();
                tPATemplate = UpdateAcceptorTree(tPATemplate, item);
            }

            sharedLog.Stop();
            return tPATemplate;
        }

        private TPATemplate UpdateAcceptorTree(TPATemplate tpa, PMTrace t)
        {
            if (t.Events.Count > 0)
            {
                TPATemplate.Node node = UpdateStartingNode(tpa, t);
                t.Events.First();
                foreach (PMEvent item in t.Events.Skip(1))
                {
                    node = UpdateNextNode(tpa, node, item);
                }

                node.IsFinalNode = true;
            }

            return tpa;
        }

        public i2TPA UpdateAcceptorTree(i2TPA tpa, PMTrace t)
        {
            var tpax = tpa.ToTPATemplate();

            UpdateAcceptorTree(tpax, t);

            return new i2TPA(tpax);

        }


        private TPATemplate.Node UpdateNextNode(TPATemplate tpa, TPATemplate.Node current, PMEvent e)
        {
            TPATemplate.Node node = (from tr in tpa.getExclusiveTransitionsfromSource(current.Id)
                                     select tr.getEndNodes(tpa).First() into n
                                     where PMLogHelper.IsEquivalent(n, e)
                                     select n).FirstOrDefault();
            if (node != null)
            {
                return node;
            }

            TPATemplate.Node node2 = new TPATemplate.Node(e);
            tpa.Nodes.Add(node2);
            TPATemplate.NodeTransition nodeTransition = new TPATemplate.NodeTransition();
            nodeTransition.SourceNodes.Add(current.Id);
            nodeTransition.EndNodes.Add(node2.Id);
            tpa.NodeTransitions.Add(nodeTransition);
            return node2;
        }

        private TPATemplate.Node UpdateStartingNode(TPATemplate tpa, PMTrace t)
        {
            PMEvent e0 = t.Events.First();
            TPATemplate.Node node = (from s in tpa.getStartingNodes()
                                     where PMLogHelper.IsEquivalent(s, e0)
                                     select s).FirstOrDefault();
            if (node != null)
            {
                return node;
            }

            TPATemplate.Node node2 = new TPATemplate.Node(e0);
            node2.IsStartingNode = true;
            tpa.Nodes.Add(node2);
            return node2;
        }

        public TPATemplate ConsecutiveMerge(TPATemplate tpa)
        {
            bool flag = true;
            while (flag)
            {
                flag = false;
                TPATemplate.NodeTransition[] array = tpa.NodeTransitions.ToArray();
                foreach (TPATemplate.NodeTransition obj in array)
                {
                    TPATemplate.Node node = obj.getSourceNodes(tpa).FirstOrDefault();
                    TPATemplate.Node node2 = obj.getEndNodes(tpa).FirstOrDefault();
                    if (node.Id != node2.Id && PMLogHelper.IsEquivalent(node, node2))
                    {
                        FuseNodes(tpa, node, node2);
                        flag = true;
                    }
                }
            }

            return tpa;
        }

        public TPATemplate BackwardMerge(TPATemplate tpa, TransitionsMergeMode mode)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Backward Merge", tpa.Nodes.Count, sl);
            while (flag)
            {
                flag = false;
                DynamicCollection<TPATemplate.Node> dynamicCollection = new DynamicCollection<TPATemplate.Node>(tpa.Nodes);
                sharedLog.Restart(dynamicCollection.Count);
                foreach (TPATemplate.Node item in dynamicCollection.Iterate())
                {
                    sharedLog.MaxEvents = dynamicCollection.Count;
                    sharedLog.NewEvent();
                    TPATemplate.Node[] n = new TPATemplate.Node[1] { item };
                    switch (mode)
                    {
                        case TransitionsMergeMode.Equivalent:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                        case TransitionsMergeMode.Inline:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                    }

                    TPATemplate.NodeTransition[] array = GetNodeTransitionsbyEndNodes(tpa, n).ToArray();
                    HashSet<TPATemplate.NodeTransition> hashSet = tpa.NodeTransitions.ToHashSet();
                    SharedLog sharedLog2 = new SharedLog("Merging Node Transitions", array.Count(), sharedLog);
                    TPATemplate.NodeTransition[] array2 = array;
                    foreach (TPATemplate.NodeTransition nt2 in array2)
                    {
                        sharedLog2.NewEvent();
                        if (!hashSet.Contains(nt2))
                        {
                            continue;
                        }

                        IEnumerable<TPATemplate.NodeTransition> enumerable = null;
                        enumerable = ((mode == TransitionsMergeMode.Inline) ? GetAccesibleTransitions(tpa, nt2, Backward: true) : array.Where((TPATemplate.NodeTransition nt) => nt != nt2));
                        foreach (TPATemplate.NodeTransition item2 in enumerable)
                        {
                            if (!hashSet.Contains(item2))
                            {
                                continue;
                            }

                            TPATemplate.Node node = nt2.getSourceNodes(tpa).First();
                            TPATemplate.Node node2 = item2.getSourceNodes(tpa).First();
                            TPATemplate.Node node3 = nt2.getEndNodes(tpa).First();
                            TPATemplate.Node node4 = item2.getEndNodes(tpa).First();
                            switch (mode)
                            {
                                case TransitionsMergeMode.Extrict:
                                    if (node != node2 && node3.Id == node4.Id && PMLogHelper.IsEquivalent(node, node2))
                                    {
                                        FuseNodes(tpa, node, node2);
                                        tpa.NodeTransitions.Remove(item2);
                                        hashSet.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                                case TransitionsMergeMode.Inline:
                                case TransitionsMergeMode.Equivalent:
                                    if (node != node2 && PMLogHelper.IsEquivalent(node3, node4) && PMLogHelper.IsEquivalent(node, node2))
                                    {
                                        FuseNodes(tpa, node, node2);
                                        if (node3 != node4)
                                        {
                                            FuseNodes(tpa, node3, node4);
                                        }

                                        tpa.NodeTransitions.Remove(item2);
                                        hashSet.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                            }
                        }
                    }

                    sharedLog2.Stop();
                    Audit(tpa);
                    RemoveRepeatedTransitions(tpa);
                }
            }

            sharedLog.Stop();
            return tpa;
        }

        public TPATemplate ForwardMerge(TPATemplate tpa, TransitionsMergeMode mode)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Forward Merge", tpa.Nodes.Count, sl);
            while (flag)
            {
                flag = false;
                DynamicCollection<TPATemplate.Node> dynamicCollection = new DynamicCollection<TPATemplate.Node>(tpa.Nodes);
                sharedLog.Restart(dynamicCollection.Count);
                foreach (TPATemplate.Node item in dynamicCollection.Iterate())
                {
                    sharedLog.MaxEvents = dynamicCollection.Count;
                    sharedLog.NewEvent();
                    TPATemplate.Node[] n = new TPATemplate.Node[1] { item };
                    switch (mode)
                    {
                        case TransitionsMergeMode.Equivalent:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                        case TransitionsMergeMode.Inline:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                    }

                    TPATemplate.NodeTransition[] array = GetNodeTransitionsbyStartingNodes(tpa, n).ToArray();
                    SharedLog sharedLog2 = new SharedLog("Merging Node Transitions", array.Count(), sharedLog);
                    TPATemplate.NodeTransition[] array2 = array;
                    foreach (TPATemplate.NodeTransition nt2 in array2)
                    {
                        sharedLog2.NewEvent();
                        if (!tpa.NodeTransitions.Contains(nt2))
                        {
                            continue;
                        }

                        IEnumerable<TPATemplate.NodeTransition> enumerable = null;
                        enumerable = ((mode == TransitionsMergeMode.Inline) ? GetAccesibleTransitions(tpa, nt2, Backward: false) : array.Where((TPATemplate.NodeTransition nt) => nt != nt2));
                        foreach (TPATemplate.NodeTransition item2 in enumerable)
                        {
                            if (!tpa.NodeTransitions.Contains(item2))
                            {
                                continue;
                            }

                            TPATemplate.Node node = nt2.getSourceNodes(tpa).First();
                            TPATemplate.Node node2 = item2.getSourceNodes(tpa).First();
                            TPATemplate.Node node3 = nt2.getEndNodes(tpa).First();
                            TPATemplate.Node node4 = item2.getEndNodes(tpa).First();
                            switch (mode)
                            {
                                case TransitionsMergeMode.Extrict:
                                    if (node3 != node4 && node.Id == node2.Id && PMLogHelper.IsEquivalent(node3, node4))
                                    {
                                        FuseNodes(tpa, node3, node4);
                                        tpa.NodeTransitions.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                                case TransitionsMergeMode.Inline:
                                case TransitionsMergeMode.Equivalent:
                                    if (node3 != node4 && PMLogHelper.IsEquivalent(node3, node4) && PMLogHelper.IsEquivalent(node, node2))
                                    {
                                        FuseNodes(tpa, node3, node4);
                                        if (node != node2)
                                        {
                                            FuseNodes(tpa, node, node2);
                                        }

                                        tpa.NodeTransitions.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                            }
                        }
                    }

                    sharedLog2.Stop();
                    Audit(tpa);
                    RemoveRepeatedTransitions(tpa);
                }
            }

            sharedLog.Stop();
            return tpa;
        }

        private IEnumerable<(TPATemplate.NodeTransition, TPATemplate.NodeTransition)> IteratePairwiseModifiableNodeTransitions(TPATemplate tpa, bool Accessible = true, bool Backward = false)
        {
            TPATemplate.NodeTransition[] array = tpa.NodeTransitions.ToArray();
            foreach (TPATemplate.NodeTransition nt0 in array)
            {
                TPATemplate.NodeTransition[] accesibleTransitions;
                if (Accessible)
                {
                    accesibleTransitions = GetAccesibleTransitions(tpa, nt0, Backward);
                    foreach (TPATemplate.NodeTransition nodeTransition in accesibleTransitions)
                    {
                        if (nt0.Id != nodeTransition.Id && tpa.NodeTransitions.Contains(nt0) && tpa.NodeTransitions.Contains(nodeTransition))
                        {
                            yield return (nt0, nodeTransition);
                        }
                    }

                    continue;
                }

                accesibleTransitions = tpa.NodeTransitions.ToArray();
                foreach (TPATemplate.NodeTransition nodeTransition2 in accesibleTransitions)
                {
                    if (nt0.Id != nodeTransition2.Id && tpa.NodeTransitions.Contains(nt0) && tpa.NodeTransitions.Contains(nodeTransition2))
                    {
                        yield return (nt0, nodeTransition2);
                    }
                }
            }
        }

        public static IEnumerable<TPATemplate.NodeTransition> GetNodeTransitionsbyStartingNodes(TPATemplate tpa, TPATemplate.Node[] n0, bool AllowParallel = false)
        {
            foreach (TPATemplate.Node node in n0)
            {
                foreach (TPATemplate.NodeTransition item in from nt in node.getOutTransitions(tpa)
                                                            where AllowParallel || !IsParallel(nt)
                                                            select nt)
                {
                    yield return item;
                }
            }
        }

        public static IEnumerable<TPATemplate.NodeTransition> GetNodeTransitionsbyEndNodes(TPATemplate tpa, TPATemplate.Node[] n0, bool AllowParallel = false)
        {
            foreach (TPATemplate.Node node in n0)
            {
                foreach (TPATemplate.NodeTransition item in from nt in node.getInTransitions(tpa)
                                                            where AllowParallel || !IsParallel(nt)
                                                            select nt)
                {
                    yield return item;
                }
            }
        }

        public static bool IsParallel(TPATemplate.NodeTransition nt)
        {
            if (nt.SourceNodes.Count <= 1)
            {
                return nt.EndNodes.Count > 1;
            }

            return true;
        }

        public static IEnumerable<TPATemplate.Node> GetEquivalentNodes(TPATemplate tpa, TPATemplate.Node n0, TPATemplate.Node[] region = null)
        {
            if (region == null)
            {
                region = tpa.Nodes.ToArray();
            }

            return region.Where((TPATemplate.Node n) => PMLogHelper.IsEquivalent(n0, n));
        }

        public static TPATemplate.NodeTransition[] GetAccesibleTransitions(TPATemplate tpa, TPATemplate.NodeTransition nt0, bool Backward)
        {
            List<TPATemplate.NodeTransition> list = new List<TPATemplate.NodeTransition>();
            if (Backward)
            {
                list.AddRange(GetBackwardTransitions(tpa, nt0.getEndNodes(tpa).First()));
            }
            else
            {
                list.AddRange(GetForwardTransitions(tpa, nt0.getSourceNodes(tpa).First()));
            }

            return list.ToArray();
        }

        public static TPATemplate.NodeTransition[] GetBackwardTransitions(TPATemplate tpa, TPATemplate.Node n0)
        {
            HashSet<TPATemplate.NodeTransition> hashSet = new HashSet<TPATemplate.NodeTransition>();
            HashSet<TPATemplate.NodeTransition> hashSet2 = new HashSet<TPATemplate.NodeTransition>(n0.getInTransitions(tpa));
            while (hashSet2.Count > 0)
            {
                TPATemplate.NodeTransition nodeTransition = hashSet2.First();
                if (!hashSet.Contains(nodeTransition))
                {
                    hashSet.Add(nodeTransition);
                    foreach (TPATemplate.NodeTransition inTransition in nodeTransition.getSourceNodes(tpa).First().getInTransitions(tpa))
                    {
                        hashSet2.Add(inTransition);
                    }
                }

                hashSet2.Remove(nodeTransition);
            }

            return hashSet.ToArray();
        }

        public static TPATemplate.Node[] GetForwardNodes(TPATemplate tpa, TPATemplate.Node n0)
        {
            return (from nt in GetForwardTransitions(tpa, n0)
                    select nt.getEndNodes(tpa).First()).ToArray();
        }

        public static TPATemplate.Node[] GetBackwardNodes(TPATemplate tpa, TPATemplate.Node n0)
        {
            return (from nt in GetBackwardTransitions(tpa, n0)
                    select nt.getSourceNodes(tpa).First()).ToArray();
        }

        public static TPATemplate.NodeTransition[] GetForwardTransitions(TPATemplate tpa, TPATemplate.Node n0)
        {
            HashSet<TPATemplate.NodeTransition> hashSet = new HashSet<TPATemplate.NodeTransition>();
            HashSet<TPATemplate.NodeTransition> hashSet2 = new HashSet<TPATemplate.NodeTransition>(n0.getOutTransitions(tpa));
            while (hashSet2.Count > 0)
            {
                TPATemplate.NodeTransition nodeTransition = hashSet2.First();
                if (!hashSet.Contains(nodeTransition))
                {
                    hashSet.Add(nodeTransition);
                    foreach (TPATemplate.NodeTransition outTransition in nodeTransition.getEndNodes(tpa).First().getOutTransitions(tpa))
                    {
                        hashSet2.Add(outTransition);
                    }
                }

                hashSet2.Remove(nodeTransition);
            }

            return hashSet.ToArray();
        }

        public static TPATemplate.NodeTransition[] GetAccesibleTransitionsOLD(TPATemplate tpa, TPATemplate.Node n0, bool Backward)
        {
            List<TPATemplate.NodeTransition> list = new List<TPATemplate.NodeTransition>();
            List<TPATemplate.NodeTransition> list2 = new List<TPATemplate.NodeTransition>();
            if (Backward)
            {
                list2.AddRange(n0.getInTransitions(tpa));
            }
            else
            {
                list2.AddRange(n0.getOutTransitions(tpa));
            }

            while (list2.Count > 0)
            {
                TPATemplate.NodeTransition nodeTransition = list2.First();
                if (!list.Contains(nodeTransition))
                {
                    list.Add(nodeTransition);
                    TPATemplate.Node node = nodeTransition.getEndNodes(tpa).First();
                    if (Backward)
                    {
                        list2.AddRange(node.getInTransitions(tpa));
                    }
                    else
                    {
                        list2.AddRange(node.getOutTransitions(tpa));
                    }
                }

                list2.Remove(nodeTransition);
            }

            return list.ToArray();
        }

        public static TPATemplate.Node[] GetAccesibleNodes(TPATemplate tpa, TPATemplate.Node n0, bool Backward)
        {
            HashSet<TPATemplate.Node> hashSet = new HashSet<TPATemplate.Node>();
            hashSet = ((!Backward) ? (from nt in GetForwardTransitions(tpa, n0)
                                      select nt.getEndNodes(tpa).First()).ToHashSet() : (from nt in GetBackwardTransitions(tpa, n0)
                                                                                         select nt.getEndNodes(tpa).First()).ToHashSet());
            return hashSet.ToArray();
        }

        private bool IsParallel(TPATemplate tpa, TPATemplate.Node[] region, TPATemplate.Node[] g)
        {
            _ = ParallelIdentificationPolicy;
            return SplitMinerIsParallelMethod(tpa, region, g);
        }

        private bool SplitMinerIsParallelMethod(TPATemplate tpa, TPATemplate.Node[] region, TPATemplate.Node[] g)
        {
            return ConcurrentNodesHelper.AreParallelSplitMiner(tpa, region, g);
        }

        private bool InductiveMinerParallelMethod(TPATemplate t, TPATemplate.Node[] region, TPATemplate.Node[] g)
        {
            foreach (TPATemplate.Node node in g)
            {
                foreach (TPATemplate.Node item in g.Except(new TPATemplate.Node[1] { node }))
                {
                    _ = item;
                    IEnumerable<TPATemplate.Node> equivalentNodes = GetEquivalentNodes(t, node, region);
                    IEnumerable<TPATemplate.Node> eq1 = GetEquivalentNodes(t, node, region);
                    bool flag = equivalentNodes.Any((TPATemplate.Node x) => eq1.Any((TPATemplate.Node y) => CutsHelper.IsBackwarded(t, x, y)));
                    bool flag2 = equivalentNodes.Any((TPATemplate.Node x) => eq1.Any((TPATemplate.Node y) => CutsHelper.IsForwarded(t, x, y)));
                    if (!flag || !flag2)
                    {
                        return false;
                    }
                }
            }

            return true;
        }

        public void SaveTPA(string name, TPATemplate tpa)
        {
            new ITPAOneFileSaver().Save("c:\\temp\\" + name + ".itpa", new MemoryTPA(tpa, new PMLog()));
        }

        public TPATemplate ParallelForwardMerge(TPATemplate tpa)
        {
            foreach (TPATemplate.Node item in new DynamicCollection<TPATemplate.Node>(tpa.Nodes).Iterate())
            {
                GetParallelHypothesis(tpa, item);
            }

            return tpa;
        }

        private TPATemplate.Node[] MoreParallels(TPATemplate tpa, TPATemplate.Node[] _region, TPATemplate.Node[] parallels)
        {
            List<TPATemplate.Node> list = new List<TPATemplate.Node>();
            bool flag = true;
            TPATemplate.Node[] array = _region.Union(parallels).ToArray();
            while (flag)
            {
                List<TPATemplate.Node> first = new List<TPATemplate.Node>();
                TPATemplate.Node[] ppars = first.Union(parallels).ToArray();
                flag = false;
                foreach (TPATemplate.Node item in array.Where((TPATemplate.Node r) => !ppars.Contains(r) && !ppars.Any((TPATemplate.Node p) => PMLogHelper.IsEquivalent(r, p))))
                {
                    if (IsParallel(tpa, array, ppars.Union(new TPATemplate.Node[1] { item }).ToArray()))
                    {
                        list.Add(item);
                        break;
                    }
                }
            }

            return list.ToArray();
        }

        private void GetParallelHypothesis(TPATemplate tpa, TPATemplate.Node n0)
        {
            TPATemplate.Node[] g2 = GetParallelFollowingNodes(tpa, n0).ToArray();
            TPATemplate.Node[] region = GetParalleForwardAccesibleNodes(tpa, n0).ToArray();
            foreach (TPATemplate.Node[] item in from x in Grouper<TPATemplate.Node>.CreateGroups(g2, (TPATemplate.Node[] g) => IsParallel(tpa, region, g)).ToArray()
                                                where x.Length > 1
                                                select x)
            {
                (TPATemplate.Node, TPATemplate.Node[])? forwardSyncronizingNode = GetForwardSyncronizingNode(tpa, n0, item);
                if (forwardSyncronizingNode.HasValue)
                {
                    TPATemplate.Node[] array = MoreParallels(tpa, forwardSyncronizingNode.Value.Item2, item);
                    if (array.Length == 0)
                    {
                        ApplyParallel(tpa, n0, item, forwardSyncronizingNode.Value.Item2, forwardSyncronizingNode.Value.Item1);
                    }
                    else
                    {
                        ApplyParallel(tpa, n0, item.Union(array).ToArray(), forwardSyncronizingNode.Value.Item2, forwardSyncronizingNode.Value.Item1);
                    }
                }
            }
        }

        private void FuseParallelEquivalentNodes(TPATemplate tpa, TPATemplate.Node[] region, TPATemplate.Node[] parallels)
        {
            foreach (TPATemplate.Node p in parallels)
            {
                TPATemplate.Node[] array = region.Where((TPATemplate.Node r) => PMLogHelper.IsEquivalent(r, p)).Except(new TPATemplate.Node[1] { p }).ToArray();
                foreach (TPATemplate.Node n in array)
                {
                    FuseNodes(tpa, p, n);
                }
            }
        }

        private void RemoveInterSplitTransitions(TPATemplate tpa, TPATemplate.Node[] region, TPATemplate.Node[][] Sequences, TPATemplate.Node[] parallels, TPATemplate.Node post)
        {
            List<TPATemplate.NodeTransition> list = new List<TPATemplate.NodeTransition>();
            foreach (TPATemplate.Node[] s2 in Sequences)
            {
                foreach (TPATemplate.Node[] item in Sequences.Where((TPATemplate.Node[] s) => s != s2))
                {
                    list.AddRange(GetInterSplitTransitions(tpa, region, s2, item, parallels, post));
                }
            }

            list.ForEach(delegate (TPATemplate.NodeTransition nt)
            {
                tpa.NodeTransitions.Remove(nt);
            });
        }

        private void RemoveParallelSelfloops(TPATemplate tpa, TPATemplate.Node[] parallels)
        {
            foreach (TPATemplate.Node p in parallels)
            {
                (from nt in p.getOutTransitions(tpa)
                 where nt.EndNodes.Count == 1 && nt.EndNodes.First() == p.Id
                 select nt).ToList().ForEach(delegate (TPATemplate.NodeTransition nt)
                 {
                     tpa.NodeTransitions.Remove(nt);
                 });
            }
        }

        private TPATemplate.Node SelectBestForwardNodeInSequence(TPATemplate tpa, TPATemplate.Node[] s0, TPATemplate.Node n0, TPATemplate.Node n1)
        {
            IEnumerable<TPATemplate.Node> source = from n in GetForwardNodes(tpa, n1)
                                                   where s0.Any((TPATemplate.Node nx) => PMLogHelper.IsEquivalent(n, nx))
                                                   select n;
            if (source.Count() == 1)
            {
                return source.First();
            }

            if (source.Count() > 1)
            {
                TPATemplate.Node[] array = source.ToArray();
                foreach (TPATemplate.Node fn0 in array)
                {
                    if (!source.Where((TPATemplate.Node f) => f != fn0).Any((TPATemplate.Node f) => CutsHelper.IsAccessible(tpa, f, fn0, backward: false)))
                    {
                        return fn0;
                    }
                }
            }

            return null;
        }

        private TPATemplate.Node SelectBestBackwardNodeInSequence(TPATemplate tpa, TPATemplate.Node[] s1, TPATemplate.Node n0, TPATemplate.Node n1)
        {
            IEnumerable<TPATemplate.Node> source = from n in GetBackwardNodes(tpa, n0)
                                                   where s1.Any((TPATemplate.Node nx) => PMLogHelper.IsEquivalent(n, nx))
                                                   select n;
            if (source.Count() == 1)
            {
                return source.First();
            }

            if (source.Count() > 1)
            {
                TPATemplate.Node[] array = source.ToArray();
                foreach (TPATemplate.Node bn0 in array)
                {
                    if (!source.Where((TPATemplate.Node f) => f != bn0).Any((TPATemplate.Node f) => CutsHelper.IsAccessible(tpa, f, bn0, backward: true)))
                    {
                        return bn0;
                    }
                }
            }

            return null;
        }

        private List<TPATemplate.NodeTransition> GetInterSplitTransitions(TPATemplate tpa, TPATemplate.Node[] region, TPATemplate.Node[] _s0, TPATemplate.Node[] _s1, TPATemplate.Node[] parallels, TPATemplate.Node post)
        {
            List<TPATemplate.NodeTransition> list = new List<TPATemplate.NodeTransition>();
            TPATemplate.Node[] array = region.Where((TPATemplate.Node x) => _s0.Any((TPATemplate.Node y) => PMLogHelper.IsEquivalent(x, y))).Union(_s0).ToArray();
            TPATemplate.Node[] array2 = region.Where((TPATemplate.Node x) => _s1.Any((TPATemplate.Node y) => PMLogHelper.IsEquivalent(x, y))).Union(_s1).ToArray();
            TPATemplate.Node[] array3 = array;
            foreach (TPATemplate.Node node in array3)
            {
                TPATemplate.Node[] array4 = array2;
                foreach (TPATemplate.Node n1 in array4)
                {
                    TPATemplate.NodeTransition nodeTransition = (from nt in node.getOutTransitions(tpa)
                                                                 where nt.EndNodes.Count == 1 && nt.EndNodes[0] == n1.Id
                                                                 select nt).FirstOrDefault();
                    if (nodeTransition == null)
                    {
                        continue;
                    }

                    TPATemplate.Node node2 = SelectBestForwardNodeInSequence(tpa, array, node, n1);
                    if (node2 != null)
                    {
                        tpa.AddNodeTransition(new Guid[1] { node.Id }, new Guid[1] { node2.Id }, "");
                    }
                    else
                    {
                        tpa.AddNodeTransition(new Guid[1] { node.Id }, new Guid[1] { post.Id }, "");
                    }

                    if (!parallels.Contains(node))
                    {
                        TPATemplate.Node node3 = SelectBestBackwardNodeInSequence(tpa, array2, node, n1);
                        if (node3 != null)
                        {
                            if (node3 != n1)
                            {
                                tpa.AddNodeTransition(new Guid[1] { node3.Id }, new Guid[1] { n1.Id }, "");
                            }
                        }
                        else
                        {
                            TPATemplate.Node node4 = _s1.First();
                            if (node4 != n1)
                            {
                                tpa.AddNodeTransition(new Guid[1] { node4.Id }, new Guid[1] { n1.Id }, "");
                            }
                        }
                    }

                    list.Add(nodeTransition);
                }
            }

            return list;
        }

        private IEnumerable<TPATemplate.Node[]> SequenceFinals(TPATemplate tpa, TPATemplate.Node[][] Sequences, TPATemplate.Node post)
        {
            List<TPATemplate.Node[]> list = new List<TPATemplate.Node[]>();
            foreach (TPATemplate.Node[] seq in Sequences)
            {
                TPATemplate.Node[] item = (from nt in post.getInTransitions(tpa)
                                           where nt.SourceNodes.Count == 1
                                           select nt.getSourceNodes(tpa).First() into n
                                           where seq.Contains(n)
                                           select n).ToArray();
                list.Add(item);
            }

            return (from x in CartesianProduct(list)
                    select x.ToArray()).ToArray();
        }

        private static IEnumerable<IEnumerable<T>> CartesianProduct<T>(IEnumerable<IEnumerable<T>> sequences)
        {
            IEnumerable<IEnumerable<T>> enumerable = new IEnumerable<T>[1] { Enumerable.Empty<T>() };
            foreach (IEnumerable<T> sequence in sequences)
            {
                IEnumerable<T> s = sequence;
                enumerable = from seq in enumerable
                             from item in s
                             select seq.Concat(new T[1] { item });
            }

            return enumerable;
        }

        private void SaveModel(TPATemplate tpa)
        {
            new ITPAOneFileSaver().Save("c:\\temp\\tpa.itpa", new MemoryTPA(tpa, new PMLog()));
        }

        public void SaveTXTTPA(string name, TPATemplate tpa)
        {
            StringBuilder stringBuilder = new StringBuilder();
            foreach (TPATemplate.Node node in tpa.Nodes)
            {
                stringBuilder.AppendLine(node.Name);
            }

            foreach (TPATemplate.NodeTransition nodeTransition in tpa.NodeTransitions)
            {
                stringBuilder.AppendLine(nodeTransition.ToString(tpa));
            }

            string text = stringBuilder.ToString();
            if (!text.Contains("[Y] => [Y2]"))
            {
                text.Contains("[X] => [X2]");
            }

            File.WriteAllText("c:\\temp\\" + name + ".txt", text);
        }

        public bool IsParallelAllowed(TPATemplate tpa, TPATemplate.Node prev, TPATemplate.Node[] parallels, TPATemplate.Node[] region, TPATemplate.Node post)
        {
            foreach (TPATemplate.NodeTransition nt2 in tpa.NodeTransitions.Where((TPATemplate.NodeTransition nt) => nt.EndNodes.Count > 1 || nt.SourceNodes.Count > 1))
            {
                nt2.ToString(tpa);
                if (region.Any((TPATemplate.Node p) => nt2.SourceNodes.Contains(p.Id) || nt2.EndNodes.Contains(p.Id)))
                {
                    return false;
                }

                if (parallels.Any((TPATemplate.Node p) => nt2.SourceNodes.Contains(p.Id) || nt2.EndNodes.Contains(p.Id)))
                {
                    return false;
                }
            }

            return true;
        }

        private void ApplyParallel(TPATemplate tpa, TPATemplate.Node prev, TPATemplate.Node[] parallels, TPATemplate.Node[] region, TPATemplate.Node post)
        {
            Dictionary<TPATemplate.Node, TPATemplate.Node[]> dictionary = SplitSequencesinsideParallel(tpa, region, parallels);
            if (dictionary != null)
            {
                TPATemplate.Node[][] sequences = dictionary.Values.Select((TPATemplate.Node[] v) => v.ToArray()).ToArray();
                RemoveInterSplitTransitions(tpa, region, sequences, parallels, post);
                RemoveRepeatedTransitions(tpa);
                FuseParallelEquivalentNodes(tpa, region, parallels);
                RemoveRepeatedTransitions(tpa);
                Audit(tpa);
                ForwardMerge(tpa, TransitionsMergeMode.Inline);
                RemoveRepeatedTransitions(tpa);
                RemoveParallelSelfloops(tpa, parallels);
                tpa.AddNodeTransition(new Guid[1] { prev.Id }, parallels.Select((TPATemplate.Node p) => p.Id).ToArray(), "");
                (from nt in prev.getOutTransitions(tpa)
                 where nt.EndNodes.Count == 1 && parallels.Select((TPATemplate.Node p) => p.Id).Contains(nt.EndNodes.First())
                 select nt).ToList().ForEach(delegate (TPATemplate.NodeTransition nt)
                 {
                     tpa.NodeTransitions.Remove(nt);
                 });
                {
                    foreach (TPATemplate.Node[] item in SequenceFinals(tpa, sequences, post))
                    {
                        tpa.AddNodeTransition(item.Select((TPATemplate.Node p) => p.Id).ToArray(), new Guid[1] { post.Id }, "");
                        foreach (TPATemplate.NodeTransition item2 in from nt in post.getInTransitions(tpa)
                                                                     where nt.SourceNodes.Count == 1
                                                                     select nt)
                        {
                            if (item.Select((TPATemplate.Node f) => f.Id).Contains(item2.SourceNodes.First()))
                            {
                                tpa.NodeTransitions.Remove(item2);
                            }
                        }
                    }

                    return;
                }
            }

            if (!IsParallelAllowed(tpa, prev, parallels, region, post))
            {
                return;
            }

            TPATemplate.Node[] array = region;
            foreach (TPATemplate.Node node in array)
            {
                CutsHelper.DeleteNode(tpa, node);
            }

            array = parallels;
            for (int i = 0; i < array.Length; i++)
            {
                _ = array[i];
            }

            foreach (TPATemplate.NodeTransition outTransition in prev.getOutTransitions(tpa))
            {
                if (outTransition.EndNodes.Count == 1 && parallels.Select((TPATemplate.Node g) => g.Id).Contains(outTransition.EndNodes.First()))
                {
                    tpa.NodeTransitions.Remove(outTransition);
                }
            }

            tpa.NodeTransitions.Add(new TPATemplate.NodeTransition
            {
                SourceNodes = new List<Guid> { prev.Id },
                EndNodes = parallels.Select((TPATemplate.Node p) => p.Id).ToList(),
                Expression = ""
            });
            tpa.NodeTransitions.Add(new TPATemplate.NodeTransition
            {
                EndNodes = new List<Guid> { post.Id },
                SourceNodes = parallels.Select((TPATemplate.Node p) => p.Id).ToList(),
                Expression = ""
            });
        }

        private Dictionary<TPATemplate.Node, TPATemplate.Node[]> SplitSequencesinsideParallel(TPATemplate tpa, TPATemplate.Node[] region, TPATemplate.Node[] parallels)
        {
            TPATemplate.Node[] array = region.Where((TPATemplate.Node n) => !parallels.Any((TPATemplate.Node h) => PMLogHelper.IsEquivalent(h, n))).ToArray();
            if (array.Length != 0)
            {
                Dictionary<TPATemplate.Node, List<TPATemplate.Node>> dictionary = parallels.ToDictionary((TPATemplate.Node p) => p, (TPATemplate.Node p) => new List<TPATemplate.Node> { p });
                TPATemplate.Node[] array2 = array;
                foreach (TPATemplate.Node node in array2)
                {
                    TPATemplate.Node[] array3 = parallels;
                    foreach (TPATemplate.Node node2 in array3)
                    {
                        if (!IsParallel(tpa, region.ToArray(), new TPATemplate.Node[2] { node2, node }))
                        {
                            dictionary[node2].Add(node);
                            break;
                        }
                    }
                }

                return dictionary.ToDictionary((KeyValuePair<TPATemplate.Node, List<TPATemplate.Node>> x) => x.Key, (KeyValuePair<TPATemplate.Node, List<TPATemplate.Node>> v) => v.Value.ToArray());
            }

            return null;
        }

        private TPATemplate.Node[] GetIsolatedParallelRegion(TPATemplate tpa, TPATemplate.Node prev, TPATemplate.Node[] parallels, TPATemplate.Node post)
        {
            List<TPATemplate.Node> first = new List<TPATemplate.Node>();
            foreach (TPATemplate.Node n in parallels)
            {
                first = first.Union(CutsHelper.GetForwardedNodesBetween2Nodes(tpa, n, post)).ToList();
            }

            List<TPATemplate.Node> list = first.Except(new TPATemplate.Node[1] { post }).ToList();
            TPATemplate.Node[] backwardedGroup = CutsHelper.GetBackwardedGroup(tpa, prev, tpa.Nodes.ToArray());
            TPATemplate.Node[] forwardedGroup = CutsHelper.GetForwardedGroup(tpa, post, tpa.Nodes.ToArray());
            List<TPATemplate.Node> list2 = list.Intersect(backwardedGroup).ToList();
            List<TPATemplate.Node> list3 = list.Intersect(forwardedGroup).ToList();
            if (list2.Count == 0 && list3.Count == 0)
            {
                return list.ToArray();
            }

            return null;
        }

        private TPATemplate.Node GetSyncroNode(TPATemplate tpa, TPATemplate.Node prev, TPATemplate.Node[] hypo)
        {
            Dictionary<TPATemplate.Node, TPATemplate.Node[]> dictionary = new Dictionary<TPATemplate.Node, TPATemplate.Node[]>();
            TPATemplate.Node[] array = hypo;
            foreach (TPATemplate.Node node in array)
            {
                dictionary[node] = (from n in GetAccesibleNodes(tpa, node, Backward: false)
                                    where !hypo.Any((TPATemplate.Node h) => PMLogHelper.IsEquivalent(h, n))
                                    select n).ToArray();
            }

            array = dictionary.Values.First();
            foreach (TPATemplate.Node x in array)
            {
                if (SyncRegionPolicy == SyncRegionMode.FirstEquivalentNode)
                {
                    TPATemplate.Node[] array2 = dictionary.Select((KeyValuePair<TPATemplate.Node, TPATemplate.Node[]> f) => f.Value.FirstOrDefault((TPATemplate.Node h) => PMLogHelper.IsEquivalent(h, x))).ToArray();
                    if (array2 == null || !array2.All((TPATemplate.Node n) => n != null))
                    {
                        continue;
                    }

                    TPATemplate.Node node2 = array2.First();
                    {
                        foreach (TPATemplate.Node item in array2.Skip(1))
                        {
                            if (node2 != item)
                            {
                                FuseNodes(tpa, node2, item);
                            }
                        }

                        return node2;
                    }
                }

                if (dictionary.All((KeyValuePair<TPATemplate.Node, TPATemplate.Node[]> f) => f.Value.Contains(x)))
                {
                    return x;
                }
            }

            return null;
        }

        private (TPATemplate.Node Sync, TPATemplate.Node[] Region)? GetForwardSyncronizingNode(TPATemplate tpa, TPATemplate.Node prev, TPATemplate.Node[] hypo)
        {
            TPATemplate.Node syncroNode = GetSyncroNode(tpa, prev, hypo);
            TPATemplate.Node[] isolatedParallelRegion = GetIsolatedParallelRegion(tpa, prev, hypo, syncroNode);
            if (isolatedParallelRegion != null)
            {
                return (syncroNode, isolatedParallelRegion);
            }

            return null;
        }

        private (TPATemplate.Node sync, TPATemplate.Node[] region)? GetSyncrofromFollowingNodes(TPATemplate tpa, TPATemplate.Node prev, TPATemplate.Node[] hypo, TPATemplate.Node[][] n)
        {
            List<TPATemplate.Node> list = null;
            foreach (TPATemplate.Node[] source in n)
            {
                IEnumerable<TPATemplate.Node> SX = source.Where((TPATemplate.Node x) => hypo.All((TPATemplate.Node h0) => !PMLogHelper.IsEquivalent(x, h0)));
                if (list == null)
                {
                    list = new List<TPATemplate.Node>();
                    list.AddRange(SX);
                    continue;
                }

                list = list.Where((TPATemplate.Node x) => SX.Any((TPATemplate.Node y) => x == y)).ToList();
            }

            foreach (TPATemplate.Node item in list)
            {
                TPATemplate.Node[] isolatedParallelRegion = GetIsolatedParallelRegion(tpa, prev, hypo, item);
                if (isolatedParallelRegion != null)
                {
                    return (item, isolatedParallelRegion);
                }
            }

            return null;
        }

        private TPATemplate.Node[] GetParalleForwardAccesibleNodes(TPATemplate tpa, TPATemplate.Node n0)
        {
            HashSet<TPATemplate.Node> hashSet = new HashSet<TPATemplate.Node>();
            Queue<TPATemplate.Node> queue = new Queue<TPATemplate.Node>();
            queue.Enqueue(n0);
            while (queue.Count > 0)
            {
                TPATemplate.Node node = queue.Dequeue();
                hashSet.Add(node);
                TPATemplate.Node[] parallelFollowingNodes = GetParallelFollowingNodes(tpa, node);
                foreach (TPATemplate.Node item in parallelFollowingNodes)
                {
                    if (!hashSet.Contains(item) && !queue.Contains(item))
                    {
                        queue.Enqueue(item);
                    }
                }
            }

            return hashSet.ToArray();
        }

        private TPATemplate.Node[] GetParallelFollowingNodes(TPATemplate tpa, TPATemplate.Node n0, int level)
        {
            HashSet<TPATemplate.Node> hashSet = GetParallelFollowingNodes(tpa, n0).ToHashSet();
            if (level == 1)
            {
                return hashSet.ToArray();
            }

            TPATemplate.Node[] array = hashSet.ToArray();
            foreach (TPATemplate.Node n in array)
            {
                TPATemplate.Node[] parallelFollowingNodes = GetParallelFollowingNodes(tpa, n, level - 1);
                foreach (TPATemplate.Node item in parallelFollowingNodes)
                {
                    hashSet.Add(item);
                }
            }

            return hashSet.ToArray();
        }

        private TPATemplate.Node[] GetParallelFollowingNodes(TPATemplate tpa, TPATemplate.Node n0)
        {
            HashSet<TPATemplate.Node> res = new HashSet<TPATemplate.Node>();
            foreach (TPATemplate.NodeTransition outTransition in n0.getOutTransitions(tpa))
            {
                outTransition.getEndNodes(tpa).ToList().ForEach(delegate (TPATemplate.Node nx)
                {
                    res.Add(nx);
                });
            }

            return res.ToArray();
        }

        private TPATemplate.Node[] GetMilestones(TPATemplate tpa)
        {
            return tpa.Nodes.Where((TPATemplate.Node n) => PMDataHelper.GetIdKeys(n).ContainsKey("_Milestone")).ToArray();
        }

        protected void FuseMilestones(TPATemplate tpa)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Fusing Milestones", tpa.Nodes.Count, sl);
            while (flag)
            {
                TPATemplate.Node[] milestones = GetMilestones(tpa);
                sharedLog.Restart(milestones.Length);
                flag = false;
                TPATemplate.Node[] array = milestones.ToArray();
                foreach (TPATemplate.Node node in array)
                {
                    sharedLog.NewEvent();
                    TPATemplate.Node[] array2 = milestones.ToArray();
                    foreach (TPATemplate.Node node2 in array2)
                    {
                        if (tpa.Nodes.Contains(node) && tpa.Nodes.Contains(node2) && node != node2 && PMLogHelper.IsEquivalent(node, node2))
                        {
                            FuseNodes(tpa, node, node2);
                            flag = true;
                        }
                    }
                }
            }

            sharedLog.Stop();
        }

        protected void FuseEndNodes(TPATemplate tpa)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Fusing Final Nodes", tpa.Nodes.Count, sl);
            while (flag)
            {
                List<TPATemplate.Node> finalNodes = tpa.getFinalNodes();
                HashSet<TPATemplate.Node> hashSet = finalNodes.ToHashSet();
                sharedLog.Restart(finalNodes.Count);
                flag = false;
                foreach (TPATemplate.Node item in finalNodes)
                {
                    sharedLog.NewEvent();
                    foreach (TPATemplate.Node item2 in finalNodes)
                    {
                        if (item != item2 && PMLogHelper.IsEquivalent(item, item2) && hashSet.Contains(item))
                        {
                            FuseNodes(tpa, item, item2);
                            hashSet.Remove(item2);
                            flag = true;
                        }
                    }
                }
            }

            sharedLog.Stop();
        }

        private void FuseNodes(TPATemplate tpa, TPATemplate.Node n0, TPATemplate.Node n1)
        {
            foreach (TPATemplate.NodeTransition inTransition in n1.getInTransitions(tpa))
            {
                inTransition.EndNodes.Remove(n1.Id);
                inTransition.EndNodes.Add(n0.Id);
            }

            foreach (TPATemplate.NodeTransition outTransition in n1.getOutTransitions(tpa))
            {
                outTransition.SourceNodes.Remove(n1.Id);
                outTransition.SourceNodes.Add(n0.Id);
            }

            tpa.Nodes.Remove(n1);
        }

        protected void RemoveRepeatedTransitionsSlow(TPATemplate tpa)
        {
            SharedLog sharedLog = new SharedLog("Removing Transitions", tpa.NodeTransitions.Count, sl);
            TPATemplate.NodeTransition[] array = tpa.NodeTransitions.ToArray();
            foreach (TPATemplate.NodeTransition nodeTransition in array)
            {
                sharedLog.NewEvent();
                TPATemplate.NodeTransition[] array2 = tpa.NodeTransitions.ToArray();
                foreach (TPATemplate.NodeTransition nodeTransition2 in array2)
                {
                    if (tpa.NodeTransitions.Contains(nodeTransition) && tpa.NodeTransitions.Contains(nodeTransition2) && nodeTransition != nodeTransition2 && nodeTransition.SourceNodes.First() == nodeTransition2.SourceNodes.First() && nodeTransition.EndNodes.First() == nodeTransition2.EndNodes.First() && nodeTransition.Expression == nodeTransition2.Expression)
                    {
                        tpa.NodeTransitions.Remove(nodeTransition2);
                    }
                }
            }

            sharedLog.Stop();
        }

        protected void RemoveRepeatedTransitions(TPATemplate tpa, TPATemplate.Node[] Region = null)
        {
            if (Region == null)
            {
                Region = tpa.Nodes.ToArray();
            }

            SharedLog sharedLog = new SharedLog("Removing Transitions Repeated", Region.Count(), sl);
            TPATemplate.Node[] array = Region;
            foreach (TPATemplate.Node node in array)
            {
                sharedLog.NewEvent();
                List<TPATemplate.Node> list = new List<TPATemplate.Node>();
                TPATemplate.NodeTransition[] array2 = node.getOutTransitions(tpa).ToArray();
                foreach (TPATemplate.NodeTransition nodeTransition in array2)
                {
                    TPATemplate.Node item = nodeTransition.getEndNodes(tpa).First();
                    if (!list.Contains(item))
                    {
                        list.Add(item);
                    }
                    else
                    {
                        tpa.NodeTransitions.Remove(nodeTransition);
                    }
                }

                list = new List<TPATemplate.Node>();
                array2 = node.getInTransitions(tpa).ToArray();
                foreach (TPATemplate.NodeTransition nodeTransition2 in array2)
                {
                    TPATemplate.Node item2 = nodeTransition2.getSourceNodes(tpa).First();
                    if (!list.Contains(item2))
                    {
                        list.Add(item2);
                    }
                    else
                    {
                        tpa.NodeTransitions.Remove(nodeTransition2);
                    }
                }
            }

            sharedLog.Stop();
        }

        public static bool Audit(TPATemplate tpa)
        {
            TPATemplate.NodeTransition[] array = tpa.NodeTransitions.ToArray();
            foreach (TPATemplate.NodeTransition nodeTransition in array)
            {
                TPATemplate.Node[] source = nodeTransition.getSourceNodes(tpa).ToArray();
                TPATemplate.Node[] source2 = nodeTransition.getEndNodes(tpa).ToArray();
                if (!source.Any((TPATemplate.Node n) => n == null) && !source2.Any((TPATemplate.Node n) => n == null))
                {
                    continue;
                }

                if (AuditCorrection)
                {
                    Guid[] array2 = nodeTransition.SourceNodes.Where((Guid id) => !tpa.Nodes.Any((TPATemplate.Node nx) => nx.Id == id)).ToArray();
                    foreach (Guid item in array2)
                    {
                        nodeTransition.SourceNodes.Remove(item);
                    }

                    array2 = nodeTransition.EndNodes.Where((Guid id) => !tpa.Nodes.Any((TPATemplate.Node nx) => nx.Id == id)).ToArray();
                    foreach (Guid item2 in array2)
                    {
                        nodeTransition.EndNodes.Remove(item2);
                    }

                    if (nodeTransition.SourceNodes.Count == 0 || nodeTransition.EndNodes.Count == 0)
                    {
                        tpa.NodeTransitions.Remove(nodeTransition);
                    }

                    TraceTask.Write(tpa, "TPA TRANSITION CORRECTED", 0, TraceEventType.Warning);
                }

                return false;
            }

            return true;
        }

        public TPATemplate DiscoveryModelTemplate(IPMLog log)
        {
            return DiscoveryModel(log).ToTPATemplate();
        }

        public virtual i2TPA DiscoveryModel(IPMLog log)
        {
            PerformanceMonitor.Instance.StartTask("Discovery");

            sl = new SharedLog("Simple PALIA", log.Count(), parentsl);

            sl?.ShowAction("Aceptor Tree");

            i2TPA res = new i2TPA(new TPATemplate() { Name = log.CorpusId });

            if (BaseTPA != null)
            {
                res = BaseTPA;

            }



            foreach (var t in log.IterateTraces())
            {
                PerformanceMonitor.Instance.StartTask("UpdateAcceptorTree");
                sl.NewEvent();

                var nx = res.Nodes.Count();
                res = UpdateAcceptorTree(res, t);
                PerformanceMonitor.Instance.EndTask("UpdateAcceptorTree");
                if (nx != res.Nodes.Count())
                {// only is there are changes
                    PerformanceMonitor.Instance.StartTask("ConsecutiveMerge");
                    res = ConsecutiveMerge(res);
                    PerformanceMonitor.Instance.EndTask("ConsecutiveMerge");

                    PerformanceMonitor.Instance.StartTask("CleanAndFuse");
                    RemoveRepeatedTransitions(res);
                    FuseEndNodes(res);
                    FuseMilestones(res);
                    PerformanceMonitor.Instance.EndTask("CleanAndFuse");
                    //First Extrict

                    PerformanceMonitor.Instance.StartTask("ProgressiveOnwardMergeCycle");
                    res = ProgressiveOnwardMergeCycle(res, TransitionsMergeMode.Extrict);

                    var transmode = MergingPolicy;

                    if (ParalelismPolicy == ParallelMode.InductivePalia && transmode != TransitionsMergeMode.Extrict)
                    {
                        transmode = TransitionsMergeMode.Inline;
                    };

                    res = ProgressiveOnwardMergeCycle(res, transmode);
                    PerformanceMonitor.Instance.EndTask("ProgressiveOnwardMergeCycle");
                }


            }

            PerformanceMonitor.Instance.StartTask("Ending");

            if (ParalelismPolicy != ParallelMode.No)
            {
                res = ParallelForwardMerge(res);

                if (MergingPolicy == TransitionsMergeMode.Equivalent)
                {
                    res = ProgressiveOnwardMergeCycle(res, MergingPolicy);
                    /*nodesnumber = int.MaxValue;
                    while (nodesnumber > res.Nodes.Count())
                    {
                        nodesnumber = res.Nodes.Count();
                        res = BackwardMerge(res, MergingPolicy);
                        res = ForwardMerge(res, MergingPolicy);
                    }*/
                }

            }

            //Audit(res);

            if (log.getMetaData().ContainsKey(InteractiveProcessDiscoveryData.KEY) &&
                log.getMetaData()[InteractiveProcessDiscoveryData.KEY] is InteractiveProcessDiscoveryData ipd)
            {
                res = discovery.InteractiveProcessDiscoveryCustomParallelism.Apply(ipd, res);
            }

            sl.Stop();
            PerformanceMonitor.Instance.EndTask("Ending");
            PerformanceMonitor.Instance.EndTask("Discovery");

            return res;

        }

        public i2TPA ConsecutiveMerge(i2TPA tpa)
        {
            bool flag = true;
            while (flag)
            {
                flag = false;
                i2NodeTransition[] array = tpa.IterateNodeTransitions().ToArray();
                foreach (i2NodeTransition obj in array)
                {
                    i2Node i2Node = obj.getSourceNodes().FirstOrDefault();
                    i2Node i2Node2 = obj.getEndNodes().FirstOrDefault();
                    if (i2Node.Id != i2Node2.Id && i2Node.IsEquivalent(i2Node, i2Node2))
                    {
                        FuseNodes(tpa, i2Node, i2Node2);
                        flag = true;
                    }
                }
            }

            return tpa;
        }

        public virtual i2TPA ProgressiveOnwardMergeCycle(i2TPA tpa, TransitionsMergeMode mode)
        {
            if (mode == TransitionsMergeMode.None)
            {
                return tpa;
            }

            OnwardMergeCycle(tpa, TransitionsMergeMode.Extrict);
            if (mode == TransitionsMergeMode.Inline || mode == TransitionsMergeMode.Equivalent)
            {
                OnwardMergeCycle(tpa, TransitionsMergeMode.Inline);
            }

            if (mode == TransitionsMergeMode.Equivalent)
            {
                OnwardMergeCycle(tpa, TransitionsMergeMode.Equivalent);
            }

            return tpa;
        }

        public virtual i2TPA OnwardMergeCycle(i2TPA tpa, TransitionsMergeMode mode)
        {

            int nodesnumber = int.MaxValue;
            while (nodesnumber > tpa.Nodes.Count())
            {
                nodesnumber = tpa.Nodes.Count();

                //sl?.ShowAction("Backward Merge");
                tpa = BackwardMerge(tpa, mode);

                //sl?.ShowAction("Forward Merge");
                tpa = ForwardMerge(tpa, mode);
            }
            return tpa;
        }

       /* public virtual i2TPA OnwardMergeCycle(i2TPA tpa, TransitionsMergeMode mode)
        {
            int num = int.MaxValue;
            while (num > tpa.Nodes.Count())
            {
                num = tpa.Nodes.Count();
                sl?.ShowAction("Backward Merge");
                tpa = BackwardMerge(tpa, mode);
                sl?.ShowAction("Forward Merge");
                tpa = ForwardMerge(tpa, mode);
            }

            return tpa;
        }*/

        public i2TPA ProgressiveBackwardMerge(i2TPA tpa, TransitionsMergeMode mode)
        {
            if (mode == TransitionsMergeMode.None)
            {
                return tpa;
            }

            BackwardMerge(tpa, TransitionsMergeMode.Extrict);
            if (mode == TransitionsMergeMode.Inline || mode == TransitionsMergeMode.Equivalent)
            {
                BackwardMerge(tpa, TransitionsMergeMode.Inline);
            }

            if (mode == TransitionsMergeMode.Equivalent)
            {
                BackwardMerge(tpa, TransitionsMergeMode.Equivalent);
            }

            return tpa;
        }

        public i2TPA ProgressiveForwardMerge(i2TPA tpa, TransitionsMergeMode mode)
        {
            if (mode == TransitionsMergeMode.None)
            {
                return tpa;
            }

            ForwardMerge(tpa, TransitionsMergeMode.Extrict);
            if (mode == TransitionsMergeMode.Inline || mode == TransitionsMergeMode.Equivalent)
            {
                ForwardMerge(tpa, TransitionsMergeMode.Inline);
            }

            if (mode == TransitionsMergeMode.Equivalent)
            {
                ForwardMerge(tpa, TransitionsMergeMode.Equivalent);
            }

            return tpa;
        }

        public i2TPA BackwardMerge(i2TPA tpa, TransitionsMergeMode mode)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Backward Merge", tpa.Nodes.Count, sl);
            while (flag)
            {
                flag = false;
                DynamicCollection<i2Node> dynamicCollection = new DynamicCollection<i2Node>(tpa.IterateNodes());
                sharedLog.Restart(dynamicCollection.Count);
                foreach (i2Node item in dynamicCollection.Iterate())
                {
                    sharedLog.MaxEvents = dynamicCollection.Count;
                    sharedLog.NewEvent();
                    i2Node[] n = new i2Node[1] { item };
                    switch (mode)
                    {
                        case TransitionsMergeMode.Equivalent:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                        case TransitionsMergeMode.Inline:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                    }

                    i2NodeTransition[] array = GetNodeTransitionsbyEndNodes(tpa, n).ToArray();
                    HashSet<i2NodeTransition> hashSet = tpa.IterateNodeTransitions().ToHashSet();
                    SharedLog sharedLog2 = new SharedLog("Merging Node Transitions", array.Count(), sharedLog);
                    i2NodeTransition[] array2 = array;
                    foreach (i2NodeTransition nt2 in array2)
                    {
                        sharedLog2.NewEvent();
                        if (!hashSet.Contains(nt2))
                        {
                            continue;
                        }

                        IEnumerable<i2NodeTransition> enumerable = null;
                        enumerable = ((mode == TransitionsMergeMode.Inline) ? GetAccesibleTransitions(tpa, nt2, Backward: true) : array.Where((i2NodeTransition nt) => nt != nt2));
                        foreach (i2NodeTransition item2 in enumerable)
                        {
                            if (!hashSet.Contains(item2))
                            {
                                continue;
                            }

                            i2Node i2Node = nt2.getSourceNodes().First();
                            i2Node i2Node2 = item2.getSourceNodes().First();
                            i2Node i2Node3 = nt2.getEndNodes().First();
                            i2Node i2Node4 = item2.getEndNodes().First();
                            switch (mode)
                            {
                                case TransitionsMergeMode.Extrict:
                                    if (i2Node != i2Node2 && i2Node3.Id == i2Node4.Id && i2Node.IsEquivalent(i2Node, i2Node2))
                                    {
                                        FuseNodes(tpa, i2Node, i2Node2);
                                        tpa.RemoveNodeTransition(item2);
                                        hashSet.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                                case TransitionsMergeMode.Inline:
                                case TransitionsMergeMode.Equivalent:
                                    if (i2Node != i2Node2 && i2Node.IsEquivalent(i2Node3, i2Node4) && i2Node.IsEquivalent(i2Node, i2Node2) && (i2Node3 != i2Node || i2Node4 != i2Node2))
                                    {
                                        FuseNodes(tpa, i2Node, i2Node2);
                                        if (i2Node3 != i2Node4)
                                        {
                                            FuseNodes(tpa, i2Node3, i2Node4);
                                        }

                                        tpa.RemoveNodeTransition(item2);
                                        hashSet.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                            }
                        }
                    }

                    sharedLog2.Stop();
                    RemoveRepeatedTransitions(tpa);
                }
            }

            sharedLog.Stop();
            return tpa;
        }

        public i2TPA ForwardMerge(i2TPA tpa, TransitionsMergeMode mode)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Forward Merge", tpa.Nodes.Count, sl);
            while (flag)
            {
                flag = false;
                DynamicCollection<i2Node> dynamicCollection = new DynamicCollection<i2Node>(tpa.IterateNodes());
                sharedLog.Restart(dynamicCollection.Count);
                foreach (i2Node item in dynamicCollection.Iterate())
                {
                    sharedLog.MaxEvents = dynamicCollection.Count;
                    sharedLog.NewEvent();
                    i2Node[] n = new i2Node[1] { item };
                    switch (mode)
                    {
                        case TransitionsMergeMode.Equivalent:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                        case TransitionsMergeMode.Inline:
                            n = GetEquivalentNodes(tpa, item).ToArray();
                            break;
                    }

                    i2NodeTransition[] array = GetNodeTransitionsbyStartingNodes(tpa, n).ToArray();
                    HashSet<i2NodeTransition> hashSet = tpa.IterateNodeTransitions().ToHashSet();
                    SharedLog sharedLog2 = new SharedLog("Merging Node Transitions", array.Count(), sharedLog);
                    i2NodeTransition[] array2 = array;
                    foreach (i2NodeTransition nt2 in array2)
                    {
                        sharedLog2.NewEvent();
                        if (!hashSet.Contains(nt2))
                        {
                            continue;
                        }

                        IEnumerable<i2NodeTransition> enumerable = null;
                        enumerable = ((mode == TransitionsMergeMode.Inline) ? GetAccesibleTransitions(tpa, nt2, Backward: false) : array.Where((i2NodeTransition nt) => nt != nt2));
                        foreach (i2NodeTransition item2 in enumerable)
                        {
                            if (!hashSet.Contains(item2))
                            {
                                continue;
                            }

                            i2Node i2Node = nt2.getSourceNodes().First();
                            i2Node i2Node2 = item2.getSourceNodes().First();
                            i2Node i2Node3 = nt2.getEndNodes().First();
                            i2Node i2Node4 = item2.getEndNodes().First();
                            switch (mode)
                            {
                                case TransitionsMergeMode.Extrict:
                                    if (i2Node3 != i2Node4 && i2Node.Id == i2Node2.Id && i2Node.IsEquivalent(i2Node3, i2Node4))
                                    {
                                        FuseNodes(tpa, i2Node3, i2Node4);
                                        tpa.RemoveNodeTransition(item2);
                                        hashSet.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                                case TransitionsMergeMode.Inline:
                                case TransitionsMergeMode.Equivalent:
                                    if (i2Node3 != i2Node4 && i2Node.IsEquivalent(i2Node3, i2Node4) && i2Node.IsEquivalent(i2Node, i2Node2) && (i2Node3 != i2Node || i2Node4 != i2Node2))
                                    {
                                        FuseNodes(tpa, i2Node3, i2Node4);
                                        if (i2Node != i2Node2)
                                        {
                                            FuseNodes(tpa, i2Node, i2Node2);
                                        }

                                        tpa.RemoveNodeTransition(item2);
                                        hashSet.Remove(item2);
                                        flag = true;
                                    }

                                    break;
                            }
                        }
                    }

                    sharedLog2.Stop();
                    RemoveRepeatedTransitions(tpa);
                }
            }

            sharedLog.Stop();
            return tpa;
        }

        public static IEnumerable<i2NodeTransition> GetNodeTransitionsbyStartingNodes(i2TPA tpa, i2Node[] n0, bool AllowParallel = false)
        {
            foreach (i2Node i2Node in n0)
            {
                foreach (i2NodeTransition item in from nt in i2Node.getOutTransitions()
                                                  where AllowParallel || !nt.IsParallel()
                                                  select nt)
                {
                    yield return item;
                }
            }
        }

        public static IEnumerable<i2NodeTransition> GetNodeTransitionsbyEndNodes(i2TPA tpa, i2Node[] n0, bool AllowParallel = false)
        {
            foreach (i2Node i2Node in n0)
            {
                foreach (i2NodeTransition item in from nt in i2Node.getInTransitions()
                                                  where AllowParallel || !nt.IsParallel()
                                                  select nt)
                {
                    yield return item;
                }
            }
        }

        public static IEnumerable<i2Node> GetEquivalentNodes(i2TPA tpa, i2Node n0, i2Node[] region = null)
        {
            if (region == null)
            {
                region = tpa.IterateNodes().ToArray();
            }

            return region.Where((i2Node n) => i2Node.IsEquivalent(n0, n));
        }

        public static i2NodeTransition[] GetAccesibleTransitions(i2TPA tpa, i2NodeTransition nt0, bool Backward)
        {
            List<i2NodeTransition> list = new List<i2NodeTransition>();
            if (Backward)
            {
                list.AddRange(GetBackwardTransitions(tpa, nt0.getEndNodes().First()));
            }
            else
            {
                list.AddRange(GetForwardTransitions(tpa, nt0.getSourceNodes().First()));
            }

            return list.ToArray();
        }

        public static i2NodeTransition[] GetBackwardTransitions(i2TPA tpa, i2Node n0)
        {
            HashSet<i2NodeTransition> hashSet = new HashSet<i2NodeTransition>();
            HashSet<i2NodeTransition> hashSet2 = new HashSet<i2NodeTransition>(n0.getInTransitions());
            while (hashSet2.Count > 0)
            {
                i2NodeTransition i2NodeTransition = hashSet2.First();
                if (!hashSet.Contains(i2NodeTransition))
                {
                    hashSet.Add(i2NodeTransition);
                    foreach (i2NodeTransition inTransition in i2NodeTransition.getSourceNodes().First().getInTransitions())
                    {
                        hashSet2.Add(inTransition);
                    }
                }

                hashSet2.Remove(i2NodeTransition);
            }

            return hashSet.ToArray();
        }

        public static i2NodeTransition[] GetForwardTransitions(i2TPA tpa, i2Node n0)
        {
            HashSet<i2NodeTransition> hashSet = new HashSet<i2NodeTransition>();
            HashSet<i2NodeTransition> hashSet2 = new HashSet<i2NodeTransition>(n0.getOutTransitions());
            while (hashSet2.Count > 0)
            {
                i2NodeTransition i2NodeTransition = hashSet2.First();
                if (!hashSet.Contains(i2NodeTransition))
                {
                    hashSet.Add(i2NodeTransition);
                    foreach (i2NodeTransition outTransition in i2NodeTransition.getEndNodes().First().getOutTransitions())
                    {
                        hashSet2.Add(outTransition);
                    }
                }

                hashSet2.Remove(i2NodeTransition);
            }

            return hashSet.ToArray();
        }

        public static i2Node[] GetAccesibleNodes(i2TPA tpa, i2Node n0, bool Backward)
        {
            HashSet<i2Node> hashSet = new HashSet<i2Node>();
            hashSet = ((!Backward) ? (from nt in GetForwardTransitions(tpa, n0)
                                      select nt.getEndNodes().First()).ToHashSet() : (from nt in GetBackwardTransitions(tpa, n0)
                                                                                      select nt.getEndNodes().First()).ToHashSet());
            return hashSet.ToArray();
        }

        private bool IsParallel(i2TPA tpa, i2Node[] region, i2Node[] g)
        {
            _ = ParallelIdentificationPolicy;
            return SplitMinerIsParallelMethod(tpa, region, g);
        }

        private bool SplitMinerIsParallelMethod(i2TPA tpa, i2Node[] region, i2Node[] g)
        {
            return ConcurrentNodesHelper.AreParallelSplitMiner(tpa, region, g);
        }

        private bool InductiveMinerParallelMethod(i2TPA t, i2Node[] region, i2Node[] g)
        {
            foreach (i2Node i2Node in g)
            {
                foreach (i2Node item in g.Except(new i2Node[1] { i2Node }))
                {
                    _ = item;
                    IEnumerable<i2Node> equivalentNodes = GetEquivalentNodes(t, i2Node, region);
                    IEnumerable<i2Node> eq1 = GetEquivalentNodes(t, i2Node, region);
                    bool flag = equivalentNodes.Any((i2Node x) => eq1.Any((i2Node y) => CutsHelper.IsBackwarded(t, x, y)));
                    bool flag2 = equivalentNodes.Any((i2Node x) => eq1.Any((i2Node y) => CutsHelper.IsForwarded(t, x, y)));
                    if (!flag || !flag2)
                    {
                        return false;
                    }
                }
            }

            return true;
        }

        public i2TPA ParallelForwardMerge(i2TPA tpa)
        {
            foreach (i2Node item in new DynamicCollection<i2Node>(tpa.IterateNodes()).Iterate())
            {
                GetParallelHypothesis(tpa, item);
            }

            return tpa;
        }

        private i2Node[] MoreParallels(i2TPA tpa, i2Node[] _region, i2Node[] parallels)
        {
            List<i2Node> list = new List<i2Node>();
            bool flag = true;
            i2Node[] array = _region.Union(parallels).ToArray();
            while (flag)
            {
                List<i2Node> first = new List<i2Node>();
                i2Node[] ppars = first.Union(parallels).ToArray();
                flag = false;
                foreach (i2Node item in array.Where((i2Node r) => !ppars.Contains(r) && !ppars.Any((i2Node p) => PMLogHelper.IsEquivalent(r, p))))
                {
                    if (IsParallel(tpa, array, ppars.Union(new i2Node[1] { item }).ToArray()))
                    {
                        list.Add(item);
                        break;
                    }
                }
            }

            return list.ToArray();
        }

        private void GetParallelHypothesis(i2TPA tpa, i2Node n0)
        {
            i2Node[] g2 = GetParallelFollowingNodes(tpa, n0).ToArray();
            i2Node[] region = GetParalleForwardAccesibleNodes(tpa, n0).ToArray();
            foreach (i2Node[] item in from x in Grouper<i2Node>.CreateGroups(g2, (i2Node[] g) => IsParallel(tpa, region, g)).ToArray()
                                      where x.Length > 1
                                      select x)
            {
                (i2Node, i2Node[])? forwardSyncronizingNode = GetForwardSyncronizingNode(tpa, n0, item);
                if (forwardSyncronizingNode.HasValue)
                {
                    i2Node[] array = MoreParallels(tpa, forwardSyncronizingNode.Value.Item2, item);
                    if (array.Length == 0)
                    {
                        ApplyParallel(tpa, n0, item, forwardSyncronizingNode.Value.Item2, forwardSyncronizingNode.Value.Item1);
                    }
                    else
                    {
                        ApplyParallel(tpa, n0, item.Union(array).ToArray(), forwardSyncronizingNode.Value.Item2, forwardSyncronizingNode.Value.Item1);
                    }
                }
            }
        }

        private void FuseParallelEquivalentNodes(i2TPA tpa, i2Node[] region, i2Node[] parallels)
        {
            foreach (i2Node p in parallels)
            {
                i2Node[] array = region.Where((i2Node r) => PMLogHelper.IsEquivalent(r, p)).Except(new i2Node[1] { p }).ToArray();
                foreach (i2Node n in array)
                {
                    FuseNodes(tpa, p, n);
                }
            }
        }

        private void RemoveInterSplitTransitions(i2TPA tpa, i2Node[] region, i2Node[][] Sequences, i2Node[] parallels, i2Node post)
        {
            List<i2NodeTransition> list = new List<i2NodeTransition>();
            foreach (i2Node[] s2 in Sequences)
            {
                foreach (i2Node[] item in Sequences.Where((i2Node[] s) => s != s2))
                {
                    list.AddRange(GetInterSplitTransitions(tpa, region, s2, item, parallels, post));
                }
            }

            list.ForEach(delegate (i2NodeTransition nt)
            {
                tpa.RemoveNodeTransition(nt);
            });
        }

        private void RemoveParallelSelfloops(i2TPA tpa, i2Node[] parallels)
        {
            foreach (i2Node p in parallels)
            {
                (from nt in p.getOutTransitions()
                 where nt.getEndNodes().Count() == 1 && nt.getEndNodes().First() == p
                 select nt).ToList().ForEach(delegate (i2NodeTransition nt)
                 {
                     tpa.RemoveNodeTransition(nt);
                 });
            }
        }

        private i2Node SelectBestForwardNodeInSequence(i2TPA tpa, i2Node[] s0, i2Node n0, i2Node n1)
        {
            IEnumerable<i2Node> source = from n in GetForwardNodes(tpa, n1)
                                         where s0.Any((i2Node nx) => PMLogHelper.IsEquivalent(n, nx))
                                         select n;
            if (source.Count() == 1)
            {
                return source.First();
            }

            if (source.Count() > 1)
            {
                i2Node[] array = source.ToArray();
                foreach (i2Node fn0 in array)
                {
                    if (!source.Where((i2Node f) => f != fn0).Any((i2Node f) => CutsHelper.IsAccessible(tpa, f, fn0, backward: false)))
                    {
                        return fn0;
                    }
                }
            }

            return null;
        }

        public static i2Node[] GetForwardNodesInRegion(i2TPA tpa, i2Node n0, i2Node[] region)
        {
            return (from n in GetForwardNodes(tpa, n0)
                    where region.Contains(n)
                    select n).ToArray();
        }

        public static i2Node[] GetBackwardNodesInRegion(i2TPA tpa, i2Node n0, i2Node[] region)
        {
            return (from n in GetBackwardNodes(tpa, n0)
                    where region.Contains(n)
                    select n).ToArray();
        }

        public static i2Node[] GetForwardNodes(i2TPA tpa, i2Node n0)
        {
            return (from nt in GetForwardTransitions(tpa, n0)
                    select nt.getEndNodes().First()).ToArray();
        }

        public static i2Node[] GetBackwardNodes(i2TPA tpa, i2Node n0)
        {
            return (from nt in GetBackwardTransitions(tpa, n0)
                    select nt.getSourceNodes().First()).ToArray();
        }

        private i2Node SelectBestBackwardNodeInSequence(i2TPA tpa, i2Node[] s1, i2Node n0, i2Node n1)
        {
            IEnumerable<i2Node> source = from n in GetBackwardNodes(tpa, n0)
                                         where s1.Any((i2Node nx) => PMLogHelper.IsEquivalent(n, nx))
                                         select n;
            if (source.Count() == 1)
            {
                return source.First();
            }

            if (source.Count() > 1)
            {
                i2Node[] array = source.ToArray();
                foreach (i2Node bn0 in array)
                {
                    if (!source.Where((i2Node f) => f != bn0).Any((i2Node f) => CutsHelper.IsAccessible(tpa, f, bn0, backward: true)))
                    {
                        return bn0;
                    }
                }
            }

            return null;
        }

        private List<i2NodeTransition> GetInterSplitTransitions(i2TPA tpa, i2Node[] region, i2Node[] _s0, i2Node[] _s1, i2Node[] parallels, i2Node post)
        {
            List<i2NodeTransition> list = new List<i2NodeTransition>();
            i2Node[] array = region.Where((i2Node x) => _s0.Any((i2Node y) => PMLogHelper.IsEquivalent(x, y))).Union(_s0).ToArray();
            i2Node[] array2 = region.Where((i2Node x) => _s1.Any((i2Node y) => PMLogHelper.IsEquivalent(x, y))).Union(_s1).ToArray();
            i2Node[] array3 = array;
            foreach (i2Node i2Node in array3)
            {
                i2Node[] array4 = array2;
                foreach (i2Node n1 in array4)
                {
                    i2NodeTransition i2NodeTransition = (from nt in i2Node.getOutTransitions()
                                                         where nt.End.Count == 1 && nt.getEndNodes().First() == n1
                                                         select nt).FirstOrDefault();
                    if (i2NodeTransition == null)
                    {
                        continue;
                    }

                    i2Node i2Node2 = SelectBestForwardNodeInSequence(tpa, array, i2Node, n1);
                    if (i2Node2 != null)
                    {
                        tpa.Addi2NodeTransition(i2Node, i2Node2);
                    }
                    else
                    {
                        tpa.Addi2NodeTransition(i2Node, post);
                    }

                    if (!parallels.Contains(i2Node))
                    {
                        i2Node i2Node3 = SelectBestBackwardNodeInSequence(tpa, array2, i2Node, n1);
                        if (i2Node3 != null)
                        {
                            if (i2Node3 != n1)
                            {
                                tpa.Addi2NodeTransition(i2Node3, n1);
                            }
                        }
                        else
                        {
                            i2Node i2Node4 = _s1.First();
                            if (i2Node4 != n1)
                            {
                                tpa.Addi2NodeTransition(i2Node4, n1);
                            }
                        }
                    }

                    list.Add(i2NodeTransition);
                }
            }

            return list;
        }

        private IEnumerable<i2Node[]> SequenceFinals(i2TPA tpa, i2Node[][] Sequences, i2Node post)
        {
            List<i2Node[]> list = new List<i2Node[]>();
            foreach (i2Node[] seq in Sequences)
            {
                i2Node[] item = (from nt in post.getInTransitions()
                                 where nt.Source.Count == 1
                                 select nt.getSourceNodes().First() into n
                                 where seq.Contains(n)
                                 select n).ToArray();
                list.Add(item);
            }

            return (from x in CartesianProduct(list)
                    select x.ToArray()).ToArray();
        }

        public bool IsParallelAllowed(i2TPA tpa, i2Node prev, i2Node[] parallels, i2Node[] region, i2Node post)
        {
            foreach (KeyValuePair<Guid, i2NodeTransition> nt2 in tpa.NodeTransitions.Where((KeyValuePair<Guid, i2NodeTransition> nt) => nt.Value.getEndNodes().Count() > 1 || nt.Value.getSourceNodes().Count() > 1))
            {
                nt2.Value.ToString();
                if (region.Any((i2Node p) => nt2.Value.getSourceNodes().Contains(p) || nt2.Value.getEndNodes().Contains(p)))
                {
                    return false;
                }

                if (parallels.Any((i2Node p) => nt2.Value.getSourceNodes().Contains(p) || nt2.Value.getEndNodes().Contains(p)))
                {
                    return false;
                }
            }

            return true;
        }

        private i2Node GetParallelfromSequences(i2TPA tpa, i2Node[] Sequence)
        {
            if (Sequence.Length == 1)
            {
                return Sequence[0];
            }

            i2Node[] array = Sequence.Where((i2Node n) => GetBackwardNodesInRegion(tpa, n, Sequence).Count() == 0).ToArray();
            if (array.Length > 1)
            {
                throw new Exception("The Parallel Sequence shoeuld have only one initial node");
            }

            return array.First();
        }

        private i2Node[] GetParallelsfromSequences(i2TPA tpa, i2Node[][] Sequences)
        {
            return Sequences.Select((i2Node[] s) => GetParallelfromSequences(tpa, s)).ToArray();
        }

        private i2Node GetPreviousFromRegion(i2TPA tpa, i2Node[] region)
        {
            HashSet<i2Node> hashSet = region.Select((i2Node n) => (from x in GetBackwardNodes(tpa, n)
                                                                   where !region.Contains(x)
                                                                   select x).First()).ToHashSet();
            if (hashSet.Count > 1)
            {
                throw new Exception("The Parallel Sequence shoeuld have only one previous node");
            }

            return hashSet.First();
        }

        private i2Node GetPosteriorFromRegion(i2TPA tpa, i2Node[] region)
        {
            HashSet<i2Node> hashSet = region.Select((i2Node n) => (from x in GetForwardNodes(tpa, n)
                                                                   where !region.Contains(x)
                                                                   select x).First()).ToHashSet();
            if (hashSet.Count > 1)
            {
                throw new Exception("The Parallel Sequence shoeuld have only one posterior node");
            }

            return hashSet.First();
        }

        public bool ApplyParallels(i2TPA tpa, i2Node[][] Sequences)
        {
            i2Node[] parallelsfromSequences = GetParallelsfromSequences(tpa, Sequences);
            return ApplyParallels(tpa, Sequences, parallelsfromSequences);
        }

        public bool ApplyParallels(i2TPA tpa, i2Node[][] Sequences, i2Node[] parallels, i2Node[][] sfin = null)
        {
            i2Node[] region = ConjunctsHelper.Union(Sequences).ToArray();
            i2Node previousFromRegion = GetPreviousFromRegion(tpa, region);
            i2Node posteriorFromRegion = GetPosteriorFromRegion(tpa, region);
            RemoveInterSplitTransitions(tpa, region, Sequences, parallels, posteriorFromRegion);
            RemoveRepeatedTransitions(tpa);
            FuseParallelEquivalentNodes(tpa, region, parallels);
            RemoveRepeatedTransitions(tpa);
            ForwardMerge(tpa, TransitionsMergeMode.Inline);
            RemoveRepeatedTransitions(tpa);
            RemoveParallelSelfloops(tpa, parallels);
            tpa.Addi2NodeTransition(previousFromRegion, parallels.Select((i2Node p) => p).ToArray());
            (from nt in previousFromRegion.getOutTransitions()
             where nt.getEndNodes().Count() == 1 && parallels.Select((i2Node p) => p).Contains(nt.getEndNodes().First())
             select nt).ToList().ForEach(delegate (i2NodeTransition nt)
             {
                 tpa.RemoveNodeTransition(nt);
             });
            if (sfin == null)
            {
                sfin = SequenceFinals(tpa, Sequences, posteriorFromRegion).ToArray();
            }

            i2Node[][] array = sfin;
            foreach (i2Node[] source in array)
            {
                tpa.Addi2NodeTransition(source.Select((i2Node p) => p).ToArray(), posteriorFromRegion);
                i2NodeTransition[] array2 = (from nt in posteriorFromRegion.getInTransitions()
                                             where nt.getSourceNodes().Count() == 1
                                             select nt).ToArray();
                foreach (i2NodeTransition i2NodeTransition in array2)
                {
                    if (source.Select((i2Node f) => f).Contains(i2NodeTransition.getSourceNodes().First()))
                    {
                        tpa.RemoveNodeTransition(i2NodeTransition);
                    }
                }
            }

            return true;
        }

        private void ApplyParallel(i2TPA tpa, i2Node prev, i2Node[] parallels, i2Node[] region, i2Node post)
        {
            Dictionary<i2Node, i2Node[]> dictionary = SplitSequencesinsideParallel(tpa, region, parallels);
            i2NodeTransition[] array;
            if (dictionary != null)
            {
                i2Node[][] sequences = dictionary.Values.Select((i2Node[] v) => v.ToArray()).ToArray();
                RemoveInterSplitTransitions(tpa, region, sequences, parallels, post);
                RemoveRepeatedTransitions(tpa);
                FuseParallelEquivalentNodes(tpa, region, parallels);
                RemoveRepeatedTransitions(tpa);
                Audit(tpa);
                ForwardMerge(tpa, TransitionsMergeMode.Inline);
                RemoveRepeatedTransitions(tpa);
                RemoveParallelSelfloops(tpa, parallels);
                tpa.Addi2NodeTransition(prev, parallels.Select((i2Node p) => p).ToArray());
                (from nt in prev.getOutTransitions()
                 where nt.getEndNodes().Count() == 1 && parallels.Select((i2Node p) => p).Contains(nt.getEndNodes().First())
                 select nt).ToList().ForEach(delegate (i2NodeTransition nt)
                 {
                     tpa.RemoveNodeTransition(nt);
                 });
                {
                    foreach (i2Node[] item in SequenceFinals(tpa, sequences, post).ToList())
                    {
                        tpa.Addi2NodeTransition(item.Select((i2Node p) => p).ToArray(), post);
                        array = (from nt in post.getInTransitions()
                                 where nt.getSourceNodes().Count() == 1
                                 select nt).ToArray();
                        foreach (i2NodeTransition i2NodeTransition in array)
                        {
                            if (item.Select((i2Node f) => f).Contains(i2NodeTransition.getSourceNodes().First()))
                            {
                                tpa.RemoveNodeTransition(i2NodeTransition);
                            }
                        }
                    }

                    return;
                }
            }

            if (!IsParallelAllowed(tpa, prev, parallels, region, post))
            {
                return;
            }

            i2Node[] array2 = region.ToArray();
            foreach (i2Node node in array2)
            {
                CutsHelper.DeleteNode(tpa, node);
            }

            array2 = parallels;
            for (int i = 0; i < array2.Length; i++)
            {
                _ = array2[i];
            }

            array = prev.getOutTransitions().ToArray();
            foreach (i2NodeTransition i2NodeTransition2 in array)
            {
                if (i2NodeTransition2.getEndNodes().Count() == 1 && parallels.Select((i2Node g) => g).Contains(i2NodeTransition2.getEndNodes().First()))
                {
                    tpa.RemoveNodeTransition(i2NodeTransition2);
                }
            }

            tpa.Addi2NodeTransition(new TPATemplate.NodeTransition
            {
                SourceNodes = new List<Guid> { prev.Id },
                EndNodes = parallels.Select((i2Node p) => p.Id).ToList(),
                Expression = ""
            });
            tpa.Addi2NodeTransition(new TPATemplate.NodeTransition
            {
                EndNodes = new List<Guid> { post.Id },
                SourceNodes = parallels.Select((i2Node p) => p.Id).ToList(),
                Expression = ""
            });
        }

        private Dictionary<i2Node, i2Node[]> SplitSequencesinsideParallel(i2TPA tpa, i2Node[] region, i2Node[] parallels)
        {
            i2Node[] array = region.Where((i2Node n) => !parallels.Any((i2Node h) => PMLogHelper.IsEquivalent(h, n))).ToArray();
            if (array.Length != 0)
            {
                Dictionary<i2Node, List<i2Node>> dictionary = parallels.ToDictionary((i2Node p) => p, (i2Node p) => new List<i2Node> { p });
                i2Node[] array2 = array;
                foreach (i2Node i2Node in array2)
                {
                    i2Node[] array3 = parallels;
                    foreach (i2Node i2Node2 in array3)
                    {
                        if (!IsParallel(tpa, region.ToArray(), new i2Node[2] { i2Node2, i2Node }))
                        {
                            dictionary[i2Node2].Add(i2Node);
                            break;
                        }
                    }
                }

                return dictionary.ToDictionary((KeyValuePair<i2Node, List<i2Node>> x) => x.Key, (KeyValuePair<i2Node, List<i2Node>> v) => v.Value.ToArray());
            }

            return null;
        }

        private i2Node[] GetIsolatedParallelRegion(i2TPA tpa, i2Node prev, i2Node[] parallels, i2Node post)
        {
            List<i2Node> first = new List<i2Node>();
            foreach (i2Node n in parallels)
            {
                first = first.Union(CutsHelper.GetForwardedNodesBetween2Nodes(tpa, n, post)).ToList();
            }

            List<i2Node> list = first.Except(new i2Node[1] { post }).ToList();
            i2Node[] backwardedGroup = CutsHelper.GetBackwardedGroup(tpa, prev, tpa.IterateNodes().ToArray());
            i2Node[] forwardedGroup = CutsHelper.GetForwardedGroup(tpa, post, tpa.IterateNodes().ToArray());
            List<i2Node> source = list.Intersect(backwardedGroup).ToList();
            List<i2Node> source2 = list.Intersect(forwardedGroup).ToList();
            if (source.Count() == 0 && source2.Count() == 0)
            {
                return list.ToArray();
            }

            return null;
        }

        private i2Node GetSyncroNode(i2TPA tpa, i2Node prev, i2Node[] hypo)
        {
            Dictionary<i2Node, i2Node[]> dictionary = new Dictionary<i2Node, i2Node[]>();
            i2Node[] array = hypo;
            foreach (i2Node i2Node in array)
            {
                dictionary[i2Node] = (from n in GetAccesibleNodes(tpa, i2Node, Backward: false)
                                      where !hypo.Any((i2Node h) => PMLogHelper.IsEquivalent(h, n))
                                      select n).ToArray();
            }

            array = dictionary.Values.First();
            foreach (i2Node x in array)
            {
                if (SyncRegionPolicy == SyncRegionMode.FirstEquivalentNode)
                {
                    i2Node[] array2 = dictionary.Select((KeyValuePair<i2Node, i2Node[]> f) => f.Value.FirstOrDefault((i2Node h) => PMLogHelper.IsEquivalent(h, x))).ToArray();
                    if (array2 == null || !array2.All((i2Node n) => n != null))
                    {
                        continue;
                    }

                    i2Node i2Node2 = array2.First();
                    {
                        foreach (i2Node item in array2.Skip(1))
                        {
                            if (i2Node2 != item)
                            {
                                FuseNodes(tpa, i2Node2, item);
                            }
                        }

                        return i2Node2;
                    }
                }

                if (dictionary.All((KeyValuePair<i2Node, i2Node[]> f) => f.Value.Contains(x)))
                {
                    return x;
                }
            }

            return null;
        }

        private (i2Node Sync, i2Node[] Region)? GetForwardSyncronizingNode(i2TPA tpa, i2Node prev, i2Node[] hypo)
        {
            i2Node syncroNode = GetSyncroNode(tpa, prev, hypo);
            i2Node[] isolatedParallelRegion = GetIsolatedParallelRegion(tpa, prev, hypo, syncroNode);
            if (isolatedParallelRegion != null)
            {
                return (syncroNode, isolatedParallelRegion);
            }

            return null;
        }

        private (i2Node sync, i2Node[] region)? GetSyncrofromFollowingNodes(i2TPA tpa, i2Node prev, i2Node[] hypo, i2Node[][] n)
        {
            List<i2Node> list = null;
            foreach (i2Node[] source in n)
            {
                IEnumerable<i2Node> SX = source.Where((i2Node x) => hypo.All((i2Node h0) => !PMLogHelper.IsEquivalent(x, h0)));
                if (list == null)
                {
                    list = new List<i2Node>();
                    list.AddRange(SX);
                    continue;
                }

                list = list.Where((i2Node x) => SX.Any((i2Node y) => x == y)).ToList();
            }

            foreach (i2Node item in list)
            {
                i2Node[] isolatedParallelRegion = GetIsolatedParallelRegion(tpa, prev, hypo, item);
                if (isolatedParallelRegion != null)
                {
                    return (item, isolatedParallelRegion);
                }
            }

            return null;
        }

        private i2Node[] GetParalleForwardAccesibleNodes(i2TPA tpa, i2Node n0)
        {
            HashSet<i2Node> hashSet = new HashSet<i2Node>();
            Queue<i2Node> queue = new Queue<i2Node>();
            queue.Enqueue(n0);
            while (queue.Count > 0)
            {
                i2Node i2Node = queue.Dequeue();
                hashSet.Add(i2Node);
                i2Node[] parallelFollowingNodes = GetParallelFollowingNodes(tpa, i2Node);
                foreach (i2Node item in parallelFollowingNodes)
                {
                    if (!hashSet.Contains(item) && !queue.Contains(item))
                    {
                        queue.Enqueue(item);
                    }
                }
            }

            return hashSet.ToArray();
        }

        private i2Node[] GetParallelFollowingNodes(i2TPA tpa, i2Node n0, int level)
        {
            HashSet<i2Node> hashSet = GetParallelFollowingNodes(tpa, n0).ToHashSet();
            if (level == 1)
            {
                return hashSet.ToArray();
            }

            i2Node[] array = hashSet.ToArray();
            foreach (i2Node n in array)
            {
                i2Node[] parallelFollowingNodes = GetParallelFollowingNodes(tpa, n, level - 1);
                foreach (i2Node item in parallelFollowingNodes)
                {
                    hashSet.Add(item);
                }
            }

            return hashSet.ToArray();
        }

        private i2Node[] GetParallelFollowingNodes(i2TPA tpa, i2Node n0)
        {
            HashSet<i2Node> res = new HashSet<i2Node>();
            foreach (i2NodeTransition outTransition in n0.getOutTransitions())
            {
                outTransition.getEndNodes().ToList().ForEach(delegate (i2Node nx)
                {
                    res.Add(nx);
                });
            }

            return res.ToArray();
        }

        private i2Node[] GetMilestones(i2TPA tpa)
        {
            return (from n in tpa.IterateNodes()
                    where i2Node.GetIdKeys(n).ContainsKey("_Milestone")
                    select n).ToArray();
        }

        private void FuseMilestones(i2TPA tpa)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Fusing Milestones", tpa.Nodes.Count, sl);
            while (flag)
            {
                i2Node[] milestones = GetMilestones(tpa);
                sharedLog.Restart(milestones.Length);
                flag = false;
                i2Node[] array = milestones.ToArray();
                foreach (i2Node i2Node in array)
                {
                    sharedLog.NewEvent();
                    i2Node[] array2 = milestones.ToArray();
                    foreach (i2Node i2Node2 in array2)
                    {
                        if (tpa.IterateNodes().Contains(i2Node) && tpa.IterateNodes().Contains(i2Node2) && i2Node != i2Node2 && i2Node.IsEquivalent(i2Node, i2Node2))
                        {
                            FuseNodes(tpa, i2Node, i2Node2);
                            flag = true;
                        }
                    }
                }
            }

            sharedLog.Stop();
        }

        private void FuseEndNodes(i2TPA tpa)
        {
            bool flag = true;
            SharedLog sharedLog = new SharedLog("Fusing Final Nodes", tpa.Nodes.Count, sl);
            while (flag)
            {
                List<i2Node> finalNodes = tpa.getFinalNodes();
                HashSet<i2Node> hashSet = finalNodes.ToHashSet();
                sharedLog.Restart(finalNodes.Count);
                flag = false;
                foreach (i2Node item in finalNodes)
                {
                    sharedLog.NewEvent();
                    foreach (i2Node item2 in finalNodes)
                    {
                        if (item != item2 && i2Node.IsEquivalent(item, item2) && hashSet.Contains(item))
                        {
                            FuseNodes(tpa, item, item2);
                            hashSet.Remove(item2);
                            flag = true;
                        }
                    }
                }
            }

            sharedLog.Stop();
        }

        private void FuseNodes(i2TPA tpa, i2Node n0, i2Node n1)
        {
            foreach (i2NodeTransition inTransition in n1.getInTransitions())
            {
                inTransition.End.Remove(n1);
                inTransition.End.Add(n0);
                n0.Input.Add(inTransition);
            }

            foreach (i2NodeTransition outTransition in n1.getOutTransitions())
            {
                outTransition.Source.Remove(n1);
                outTransition.Source.Add(n0);
                n0.Output.Add(outTransition);
            }

            tpa.RemoveNode(n1);
        }

        private void RemoveRepeatedTransitions(i2TPA tpa, i2Node[] Region = null)
        {
            if (Region == null)
            {
                Region = tpa.IterateNodes().ToArray();
            }

            SharedLog sharedLog = new SharedLog("Removing Transitions Repeated", Region.Count(), sl);
            i2Node[] array = Region;
            foreach (i2Node i2Node in array)
            {
                sharedLog.NewEvent();
                List<i2Node> list = new List<i2Node>();
                i2NodeTransition[] array2 = i2Node.getOutTransitions().ToArray();
                foreach (i2NodeTransition i2NodeTransition in array2)
                {
                    i2Node item = i2NodeTransition.getEndNodes().First();
                    if (!list.Contains(item))
                    {
                        list.Add(item);
                    }
                    else
                    {
                        tpa.RemoveNodeTransition(i2NodeTransition);
                    }
                }

                list = new List<i2Node>();
                array2 = i2Node.getInTransitions().ToArray();
                foreach (i2NodeTransition i2NodeTransition2 in array2)
                {
                    i2Node item2 = i2NodeTransition2.getSourceNodes().First();
                    if (!list.Contains(item2))
                    {
                        list.Add(item2);
                    }
                    else
                    {
                        tpa.RemoveNodeTransition(i2NodeTransition2);
                    }
                }
            }

            sharedLog.Stop();
        }

        public static bool Audit(i2TPA tpa)
        {
            return true;
        }
    }
}
