using pm4h.data;
using pm4h.discovery;
using pm4h.layout;
using pm4h.runner.logprocessor;
using pm4h.runner;
using pm4h.tpa.ipi;
using pm4h.tpa;
using pm4h.ui.fragments.tpaviewer.layout;
using pm4h.utils;
using System;
using System.Collections.Generic;
using System.Linq;
using System.Text;
using System.Threading.Tasks;
using pm4h.algorithm.i2palia;
using pm4h.algorithm.palia.Core.ipalia;
using pm4h.common;
using Sabien.Portable.Utils;
using com.espertech.esper.compat;
using System.DirectoryServices.ActiveDirectory;
using pm4h.IPALIA;
using TransitionsMergeMode = pm4h.algorithm.i2palia.TransitionsMergeMode;
using ParallelMode = pm4h.algorithm.i2palia.ParallelMode;
using SyncRegionMode = pm4h.algorithm.i2palia.SyncRegionMode;
using Grpc.Net.Client.Configuration;

namespace pm4h.IPALIAFederatedAlgorithms
{
    [RunnerElement(Name = "IPalia Federated Discovery", Description = "", Maturity = MaturityFlags.Beta, RequiredRole = pm4h.runner.security.PMAppUserRole.ProcessMiner)]
    public class IPaliaFederatedDiscovery : BasicProcessDiscovery
    {

        [RunnerExternalResourceFile(Name = "Model", Domain = new string[] { "ITPA Files (*.itpa)|*.itpa" })]
        public IVirtualIO Model { get; set; }


        [SelectionRunnerProperty(DataEnum = typeof(TransitionsMergeMode), Level = RunnerPropertyLevel.Optional)]
        public TransitionsMergeMode MergingPolicy { get; set; }

        [SelectionRunnerProperty(DataEnum = typeof(ParallelMode), Level = RunnerPropertyLevel.Optional)]
        public ParallelMode ParalelismPolicy { get; set; }

        [SelectionRunnerProperty(DataEnum = typeof(SyncRegionMode), Level = RunnerPropertyLevel.Optional)]
        public SyncRegionMode SyncNodePolicy { get; set; }


        public static IAutomaticLayout Layout = new SpringForcesLayout(500, 10, 10);

        public override iTPAModel Discovery(IPMLog l)
        {
            IPaliaFederatedAlgorithm ip = new IPaliaFederatedAlgorithm();

            TPATemplate tpauz = new TPATemplate() { Name = l.CorpusId};
            var t2 = TPATemplate.FromJson(Model.ReadAllText());
            tpauz.Nodes = t2.Nodes;
            tpauz.NodeTransitions = t2.NodeTransitions;

            ip.BaseTPA = new i2TPA(tpauz);

            ip.MergingPolicy = MergingPolicy;
            ip.ParalelismPolicy = ParalelismPolicy;
            ip.SyncRegionPolicy = SyncNodePolicy;

            parentSL = new SharedLog("IPalia", 1);
            ip.SetParentLog(parentSL);
            var tpa = ip.DiscoveryModelTemplate(l);
            MergeMetadata(l, tpa);
            parentSL.Stop();

            /*SpringForcesLayout sfl = new SpringForcesLayout(500, 10, 10);
            sfl.ComputeLayout(new TPATemplateGUI(tpa));*/
            Layout.ComputeLayout(tpa);
            tpa.Name = l.CorpusId;
            iTPAModel m = new MemoryTPA(tpa, l);

            //Processors.Clear();


            m = ReDiscoveryLogProcessorv2.Rediscover(l, m);
            return m;
        }

        public void MergeMetadata(IPMLog log, TPATemplate t)
        {
            foreach (var d in log.getMetaData())
            {
                t.Metadata[d.Key] = d.Value;
            }
        }
    }





    /// <summary>
    /// Cambia el flujo de PALIA y lo hace para que añada traza a traza de forma federada
    /// </summary>
    public class IPaliaFederatedAlgorithm : I2PaliaFederated
    {


    }

}
