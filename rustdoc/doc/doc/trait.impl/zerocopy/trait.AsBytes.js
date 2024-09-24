(function() {var implementors = {
"oak_dice":[["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.Evidence.html\" title=\"struct oak_dice::evidence::Evidence\">Evidence</a><div class=\"where\">where\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.RootLayerEvidence.html\" title=\"struct oak_dice::evidence::RootLayerEvidence\">RootLayerEvidence</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.LayerEvidence.html\" title=\"struct oak_dice::evidence::LayerEvidence\">LayerEvidence</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.ApplicationKeys.html\" title=\"struct oak_dice::evidence::ApplicationKeys\">ApplicationKeys</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.Evidence.html\" title=\"struct oak_dice::evidence::Evidence\">Evidence</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.CompoundDeviceIdentifier.html\" title=\"struct oak_dice::evidence::CompoundDeviceIdentifier\">CompoundDeviceIdentifier</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">32</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.CompoundDeviceIdentifier.html\" title=\"struct oak_dice::evidence::CompoundDeviceIdentifier\">CompoundDeviceIdentifier</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.LayerEvidence.html\" title=\"struct oak_dice::evidence::LayerEvidence\">LayerEvidence</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">1024</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.LayerEvidence.html\" title=\"struct oak_dice::evidence::LayerEvidence\">LayerEvidence</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.RootLayerEvidence.html\" title=\"struct oak_dice::evidence::RootLayerEvidence\">RootLayerEvidence</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">2048</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">256</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.RootLayerEvidence.html\" title=\"struct oak_dice::evidence::RootLayerEvidence\">RootLayerEvidence</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.Stage0DiceData.html\" title=\"struct oak_dice::evidence::Stage0DiceData\">Stage0DiceData</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.RootLayerEvidence.html\" title=\"struct oak_dice::evidence::RootLayerEvidence\">RootLayerEvidence</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.LayerEvidence.html\" title=\"struct oak_dice::evidence::LayerEvidence\">LayerEvidence</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.CertificateAuthority.html\" title=\"struct oak_dice::evidence::CertificateAuthority\">CertificateAuthority</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.CompoundDeviceIdentifier.html\" title=\"struct oak_dice::evidence::CompoundDeviceIdentifier\">CompoundDeviceIdentifier</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">640</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.Stage0DiceData.html\" title=\"struct oak_dice::evidence::Stage0DiceData\">Stage0DiceData</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.CertificateAuthority.html\" title=\"struct oak_dice::evidence::CertificateAuthority\">CertificateAuthority</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">64</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.CertificateAuthority.html\" title=\"struct oak_dice::evidence::CertificateAuthority\">CertificateAuthority</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.ApplicationPrivateKeys.html\" title=\"struct oak_dice::evidence::ApplicationPrivateKeys\">ApplicationPrivateKeys</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">64</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.ApplicationPrivateKeys.html\" title=\"struct oak_dice::evidence::ApplicationPrivateKeys\">ApplicationPrivateKeys</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.RestrictedKernelDiceData.html\" title=\"struct oak_dice::evidence::RestrictedKernelDiceData\">RestrictedKernelDiceData</a><div class=\"where\">where\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.Evidence.html\" title=\"struct oak_dice::evidence::Evidence\">Evidence</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_dice/evidence/struct.ApplicationPrivateKeys.html\" title=\"struct oak_dice::evidence::ApplicationPrivateKeys\">ApplicationPrivateKeys</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.RestrictedKernelDiceData.html\" title=\"struct oak_dice::evidence::RestrictedKernelDiceData\">RestrictedKernelDiceData</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_dice/evidence/struct.ApplicationKeys.html\" title=\"struct oak_dice::evidence::ApplicationKeys\">ApplicationKeys</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">1024</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_dice/evidence/struct.ApplicationKeys.html\" title=\"struct oak_dice::evidence::ApplicationKeys\">ApplicationKeys</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"]],
"oak_linux_boot_params":[["impl AsBytes for <a class=\"struct\" href=\"oak_linux_boot_params/struct.BootE820Entry.html\" title=\"struct oak_linux_boot_params::BootE820Entry\">BootE820Entry</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.usize.html\">usize</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_linux_boot_params/struct.SetupHeader.html\" title=\"struct oak_linux_boot_params::SetupHeader\">SetupHeader</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,</div>"]],
"oak_sev_guest":[["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/guest/struct.KeyResponse.html\" title=\"struct oak_sev_guest::guest::KeyResponse\">KeyResponse</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">28</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">32</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/guest/struct.KeyResponse.html\" title=\"struct oak_sev_guest::guest::KeyResponse\">KeyResponse</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.VmsaPage.html\" title=\"struct oak_sev_guest::vmsa::VmsaPage\">VmsaPage</a><div class=\"where\">where\n    <a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.Vmsa.html\" title=\"struct oak_sev_guest::vmsa::Vmsa\">Vmsa</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">2104</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.VmsaPage.html\" title=\"struct oak_sev_guest::vmsa::VmsaPage\">VmsaPage</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/guest/struct.AuthenticatedHeader.html\" title=\"struct oak_sev_guest::guest::AuthenticatedHeader\">AuthenticatedHeader</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">35</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/guest/struct.AuthenticatedHeader.html\" title=\"struct oak_sev_guest::guest::AuthenticatedHeader\">AuthenticatedHeader</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/guest/struct.GuestMessage.html\" title=\"struct oak_sev_guest::guest::GuestMessage\">GuestMessage</a><div class=\"where\">where\n    <a class=\"struct\" href=\"oak_sev_guest/guest/struct.GuestMessageHeader.html\" title=\"struct oak_sev_guest::guest::GuestMessageHeader\">GuestMessageHeader</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">4000</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/guest/struct.GuestMessage.html\" title=\"struct oak_sev_guest::guest::GuestMessage\">GuestMessage</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.SegmentRegister.html\" title=\"struct oak_sev_guest::vmsa::SegmentRegister\">SegmentRegister</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.SegmentRegister.html\" title=\"struct oak_sev_guest::vmsa::SegmentRegister\">SegmentRegister</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/guest/struct.GuestMessageHeader.html\" title=\"struct oak_sev_guest::guest::GuestMessageHeader\">GuestMessageHeader</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">32</a>]: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_sev_guest/guest/struct.AuthenticatedHeader.html\" title=\"struct oak_sev_guest::guest::AuthenticatedHeader\">AuthenticatedHeader</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/guest/struct.GuestMessageHeader.html\" title=\"struct oak_sev_guest::guest::GuestMessageHeader\">GuestMessageHeader</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/guest/struct.AttestationRequest.html\" title=\"struct oak_sev_guest::guest::AttestationRequest\">AttestationRequest</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">64</a>]: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">28</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/guest/struct.AttestationRequest.html\" title=\"struct oak_sev_guest::guest::AttestationRequest\">AttestationRequest</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.Vmsa.html\" title=\"struct oak_sev_guest::vmsa::Vmsa\">Vmsa</a><div class=\"where\">where\n    <a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.SegmentRegister.html\" title=\"struct oak_sev_guest::vmsa::SegmentRegister\">SegmentRegister</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">104</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">24</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">32</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">80</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">16</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">256</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/vmsa/struct.Vmsa.html\" title=\"struct oak_sev_guest::vmsa::Vmsa\">Vmsa</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/guest/struct.AttestationResponse.html\" title=\"struct oak_sev_guest::guest::AttestationResponse\">AttestationResponse</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">24</a>]: AsBytes,\n    AttestationReport: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/guest/struct.AttestationResponse.html\" title=\"struct oak_sev_guest::guest::AttestationResponse\">AttestationResponse</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_guest/guest/struct.KeyRequest.html\" title=\"struct oak_sev_guest::guest::KeyRequest\">KeyRequest</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_guest/guest/struct.KeyRequest.html\" title=\"struct oak_sev_guest::guest::KeyRequest\">KeyRequest</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"]],
"oak_sev_snp_attestation_report":[["impl AsBytes for <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.EcdsaSignature.html\" title=\"struct oak_sev_snp_attestation_report::EcdsaSignature\">EcdsaSignature</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">72</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">368</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.EcdsaSignature.html\" title=\"struct oak_sev_snp_attestation_report::EcdsaSignature\">EcdsaSignature</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.GuestPolicy.html\" title=\"struct oak_sev_snp_attestation_report::GuestPolicy\">GuestPolicy</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.GuestPolicy.html\" title=\"struct oak_sev_snp_attestation_report::GuestPolicy\">GuestPolicy</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.TcbVersion.html\" title=\"struct oak_sev_snp_attestation_report::TcbVersion\">TcbVersion</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">4</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.TcbVersion.html\" title=\"struct oak_sev_snp_attestation_report::TcbVersion\">TcbVersion</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.AttestationReportData.html\" title=\"struct oak_sev_snp_attestation_report::AttestationReportData\">AttestationReportData</a><div class=\"where\">where\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u32.html\">u32</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.GuestPolicy.html\" title=\"struct oak_sev_snp_attestation_report::GuestPolicy\">GuestPolicy</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">16</a>]: AsBytes,\n    <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.TcbVersion.html\" title=\"struct oak_sev_snp_attestation_report::TcbVersion\">TcbVersion</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">64</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">48</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">32</a>]: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">24</a>]: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>: AsBytes,\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">168</a>]: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.AttestationReportData.html\" title=\"struct oak_sev_snp_attestation_report::AttestationReportData\">AttestationReportData</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.AttestationReport.html\" title=\"struct oak_sev_snp_attestation_report::AttestationReport\">AttestationReport</a><div class=\"where\">where\n    <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.AttestationReportData.html\" title=\"struct oak_sev_snp_attestation_report::AttestationReportData\">AttestationReportData</a>: AsBytes,\n    <a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.EcdsaSignature.html\" title=\"struct oak_sev_snp_attestation_report::EcdsaSignature\">EcdsaSignature</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"oak_sev_snp_attestation_report/struct.AttestationReport.html\" title=\"struct oak_sev_snp_attestation_report::AttestationReport\">AttestationReport</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"]],
"snp_measurement":[["impl AsBytes for <a class=\"struct\" href=\"snp_measurement/page/struct.PageInfo.html\" title=\"struct snp_measurement::page::PageInfo\">PageInfo</a><div class=\"where\">where\n    [<a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>; <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.array.html\">48</a>]: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u16.html\">u16</a>: AsBytes,\n    <a class=\"enum\" href=\"snp_measurement/page/enum.PageType.html\" title=\"enum snp_measurement::page::PageType\">PageType</a>: AsBytes,\n    <a class=\"enum\" href=\"snp_measurement/page/enum.ImiPage.html\" title=\"enum snp_measurement::page::ImiPage\">ImiPage</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u8.html\">u8</a>: AsBytes,\n    <a class=\"primitive\" href=\"https://doc.rust-lang.org/nightly/std/primitive.u64.html\">u64</a>: AsBytes,\n    HasPadding&lt;<a class=\"struct\" href=\"snp_measurement/page/struct.PageInfo.html\" title=\"struct snp_measurement::page::PageInfo\">PageInfo</a>, { _ }&gt;: ShouldBe&lt;false&gt;,</div>"],["impl AsBytes for <a class=\"enum\" href=\"snp_measurement/page/enum.PageType.html\" title=\"enum snp_measurement::page::PageType\">PageType</a>"],["impl AsBytes for <a class=\"enum\" href=\"snp_measurement/page/enum.ImiPage.html\" title=\"enum snp_measurement::page::ImiPage\">ImiPage</a>"]]
};if (window.register_implementors) {window.register_implementors(implementors);} else {window.pending_implementors = implementors;}})()