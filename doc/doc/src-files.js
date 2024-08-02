var srcIndex = new Map(JSON.parse('[\
["echo",["",[],["lib.rs"]]],\
["invalid_module",["",[],["lib.rs"]]],\
["key_value_lookup",["",[],["lib.rs"]]],\
["lookup_data_generator",["",[],["data.rs","lib.rs"]]],\
["micro_rpc",["",[],["lib.rs","status.rs"]]],\
["micro_rpc_build",["",[],["lib.rs","prost.rs"]]],\
["oak_attestation",["",[],["dice.rs","handler.rs","lib.rs"]]],\
["oak_attestation_explain",["",[],["json_serialization.rs","lib.rs"]]],\
["oak_attestation_explain_cli",["",[],["main.rs"]]],\
["oak_attestation_explain_wasm",["",[],["lib.rs"]]],\
["oak_attestation_verification",["",[],["amd.rs","claims.rs","endorsement.rs","lib.rs","rekor.rs","util.rs","verifier.rs"]]],\
["oak_attestation_verification_test_utils",["",[],["lib.rs"]]],\
["oak_channel",["",[],["basic_framed.rs","client.rs","frame.rs","lib.rs","message.rs","server.rs"]]],\
["oak_client",["",[],["client.rs","lib.rs","transport.rs","verifier.rs"]]],\
["oak_containers_agent",["",[],["lib.rs","metrics.rs"]]],\
["oak_containers_hello_world_untrusted_app",["",[],["app_client.rs","demo_transport.rs","http_service.rs","lib.rs","service.rs"]]],\
["oak_containers_hello_world_web_client",["",[],["lib.rs"]]],\
["oak_containers_launcher",["",[],["lib.rs","qemu.rs","server.rs"]]],\
["oak_containers_orchestrator",["",[],["cdi.rs","container_runtime.rs","crypto.rs","dice.rs","ipc_server.rs","key_provisioning.rs","launcher_client.rs","lib.rs","logging.rs"]]],\
["oak_containers_sdk",["",[],["crypto.rs","lib.rs","oak_session_context.rs","orchestrator_client.rs","tonic.rs"]]],\
["oak_containers_stage1",["",[],["client.rs","dice.rs","image.rs","main.rs"]]],\
["oak_containers_syslogd",["",[],["log_relay.rs","main.rs","systemd_journal.rs"]]],\
["oak_core",["",[],["lib.rs","samplestore.rs","sync.rs","timer.rs"]]],\
["oak_crypto",["",[["hpke",[],["aead.rs","mod.rs"]],["noise_handshake",[],["client.rs","crypto_wrapper.rs","error.rs","mod.rs","noise.rs"]]],["encryption_key.rs","encryptor.rs","identity_key.rs","lib.rs","signer.rs","verifier.rs"]]],\
["oak_debug_service",["",[],["lib.rs"]]],\
["oak_dice",["",[],["cert.rs","evidence.rs","lib.rs","utils.rs"]]],\
["oak_echo_linux_init",["",[],["init.rs","main.rs"]]],\
["oak_echo_service",["",[],["lib.rs"]]],\
["oak_enclave_runtime_support",["",[],["heap.rs","lib.rs","libm.rs"]]],\
["oak_functions_abi",["",[],["lib.rs"]]],\
["oak_functions_client",["",[],["lib.rs"]]],\
["oak_functions_containers_app",["",[],["lib.rs","native_handler.rs"]]],\
["oak_functions_containers_launcher",["",[],["lib.rs","lookup.rs","server.rs"]]],\
["oak_functions_enclave_service",["",[],["lib.rs"]]],\
["oak_functions_launcher",["",[],["lib.rs","lookup.rs","server.rs"]]],\
["oak_functions_sdk",["",[],["lib.rs"]]],\
["oak_functions_sdk_abi_test_get_storage_item",["",[],["lib.rs"]]],\
["oak_functions_sdk_abi_test_invoke_testing",["",[],["lib.rs"]]],\
["oak_functions_service",["",[["wasm",[],["api.rs","mod.rs","wasmtime.rs"]]],["instance.rs","lib.rs","logger.rs","lookup.rs","lookup_htbl.rs"]]],\
["oak_functions_test_module",["",[],["lib.rs"]]],\
["oak_functions_test_utils",["",[],["lib.rs"]]],\
["oak_grpc",["",[],["lib.rs"]]],\
["oak_grpc_utils",["",[],["lib.rs"]]],\
["oak_hello_world_linux_init",["",[],["init.rs","main.rs"]]],\
["oak_hello_world_proto",["",[],["lib.rs"]]],\
["oak_kernel_measurement",["",[],["main.rs"]]],\
["oak_launcher_utils",["",[],["channel.rs","launcher.rs","lib.rs"]]],\
["oak_linux_boot_params",["",[],["lib.rs"]]],\
["oak_micro_rpc",["",[],["lib.rs"]]],\
["oak_proto_rust",["",[],["lib.rs"]]],\
["oak_restricted_kernel",["",[["boot",[],["mod.rs"]],["mm",[],["bitmap_frame_allocator.rs","encrypted_mapper.rs","frame_allocator.rs","mod.rs","page_tables.rs","virtual_address_allocator.rs"]],["syscall",[],["channel.rs","create_process.rs","dice_data.rs","fd.rs","key.rs","mmap.rs","mod.rs","process.rs","stdio.rs","switch_process.rs"]]],["acpi.rs","args.rs","avx.rs","descriptors.rs","elf.rs","ghcb.rs","interrupts.rs","lib.rs","libm.rs","logging.rs","memory.rs","processes.rs","shutdown.rs","snp.rs","virtio.rs"]]],\
["oak_restricted_kernel_dice",["",[],["lib.rs"]]],\
["oak_restricted_kernel_interface",["",[],["errno.rs","lib.rs","raw_syscall.rs","syscall.rs","syscalls.rs"]]],\
["oak_restricted_kernel_launcher",["",[],["lib.rs"]]],\
["oak_restricted_kernel_orchestrator",["",[],["lib.rs"]]],\
["oak_restricted_kernel_sdk",["",[],["attestation.rs","channel.rs","crypto.rs","lib.rs","testing.rs","utils.rs"]]],\
["oak_session",["",[],["attestation.rs","config.rs","encryptors.rs","handshake.rs","lib.rs","session.rs"]]],\
["oak_sev_guest",["",[],["ap_jump_table.rs","cpuid.rs","crypto.rs","ghcb.rs","guest.rs","instructions.rs","interrupts.rs","io.rs","lib.rs","msr.rs","secrets.rs","vmsa.rs"]]],\
["oak_sev_snp_attestation_report",["",[],["lib.rs"]]],\
["oak_simple_io",["",[],["lib.rs"]]],\
["oak_stage0",["",[["hal",[["base",[],["cpuid.rs","mmio.rs","mod.rs"]],["sev",[],["accept_memory.rs","cpuid.rs","mmio.rs","mod.rs","msr.rs","port.rs"]]],["mod.rs"]]],["acpi.rs","acpi_tables.rs","allocator.rs","apic.rs","cmos.rs","dice_attestation.rs","fw_cfg.rs","initramfs.rs","kernel.rs","lib.rs","logging.rs","msr.rs","paging.rs","pic.rs","sev.rs","smp.rs","zero_page.rs"]]],\
["oak_stage0_dice",["",[],["lib.rs"]]],\
["oak_tdx_guest",["",[],["lib.rs","tdcall.rs","vmcall.rs"]]],\
["oak_virtio",["",[["console",[],["mod.rs"]],["queue",[],["mod.rs","virtq.rs"]],["vsock",[["socket",[],["mod.rs"]]],["mod.rs","packet.rs"]]],["lib.rs"]]],\
["sev_serial",["",[],["lib.rs"]]],\
["snp_measurement",["",[],["main.rs","page.rs","stage0.rs","vmsa.rs"]]]\
]'));
createSrcSidebar();
