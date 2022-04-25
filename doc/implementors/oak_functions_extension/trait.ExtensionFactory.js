(function() {var implementors = {};
implementors["oak_functions_loader"] = [{"text":"impl <a class=\"trait\" href=\"oak_functions_extension/trait.ExtensionFactory.html\" title=\"trait oak_functions_extension::ExtensionFactory\">ExtensionFactory</a>&lt;<a class=\"struct\" href=\"oak_functions_loader/logger/struct.Logger.html\" title=\"struct oak_functions_loader::logger::Logger\">Logger</a>&gt; for <a class=\"struct\" href=\"oak_functions_loader/testing/struct.TestingFactory.html\" title=\"struct oak_functions_loader::testing::TestingFactory\">TestingFactory</a>","synthetic":false,"types":["oak_functions_loader::testing::TestingFactory"]}];
implementors["oak_functions_lookup"] = [{"text":"impl&lt;L&gt; <a class=\"trait\" href=\"oak_functions_extension/trait.ExtensionFactory.html\" title=\"trait oak_functions_extension::ExtensionFactory\">ExtensionFactory</a>&lt;L&gt; for <a class=\"struct\" href=\"oak_functions_lookup/struct.LookupFactory.html\" title=\"struct oak_functions_lookup::LookupFactory\">LookupFactory</a>&lt;L&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;L: <a class=\"trait\" href=\"oak_logger/trait.OakLogger.html\" title=\"trait oak_logger::OakLogger\">OakLogger</a> + 'static,&nbsp;</span>","synthetic":false,"types":["oak_functions_lookup::LookupFactory"]}];
implementors["oak_functions_metrics"] = [{"text":"impl&lt;L&gt; <a class=\"trait\" href=\"oak_functions_extension/trait.ExtensionFactory.html\" title=\"trait oak_functions_extension::ExtensionFactory\">ExtensionFactory</a>&lt;L&gt; for <a class=\"struct\" href=\"oak_functions_metrics/struct.PrivateMetricsProxyFactory.html\" title=\"struct oak_functions_metrics::PrivateMetricsProxyFactory\">PrivateMetricsProxyFactory</a>&lt;L&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;L: <a class=\"trait\" href=\"oak_logger/trait.OakLogger.html\" title=\"trait oak_logger::OakLogger\">OakLogger</a> + 'static,&nbsp;</span>","synthetic":false,"types":["oak_functions_metrics::PrivateMetricsProxyFactory"]}];
implementors["oak_functions_tf_inference"] = [{"text":"impl&lt;L&gt; <a class=\"trait\" href=\"oak_functions_extension/trait.ExtensionFactory.html\" title=\"trait oak_functions_extension::ExtensionFactory\">ExtensionFactory</a>&lt;L&gt; for <a class=\"struct\" href=\"oak_functions_tf_inference/struct.TensorFlowFactory.html\" title=\"struct oak_functions_tf_inference::TensorFlowFactory\">TensorFlowFactory</a>&lt;L&gt; <span class=\"where fmt-newline\">where<br>&nbsp;&nbsp;&nbsp;&nbsp;L: <a class=\"trait\" href=\"oak_logger/trait.OakLogger.html\" title=\"trait oak_logger::OakLogger\">OakLogger</a> + 'static,&nbsp;</span>","synthetic":false,"types":["oak_functions_tf_inference::TensorFlowFactory"]}];
if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()