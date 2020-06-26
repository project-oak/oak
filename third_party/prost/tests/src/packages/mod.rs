//! Tests nested packages.

include!(concat!(env!("OUT_DIR"), "/packages.rs"));

pub mod gizmo {
    include!(concat!(env!("OUT_DIR"), "/packages.gizmo.rs"));
}

pub mod widget {
    include!(concat!(env!("OUT_DIR"), "/packages.widget.rs"));
    pub mod factory {
        include!(concat!(env!("OUT_DIR"), "/packages.widget.factory.rs"));
    }
}

// Trait used in extern_paths.rs.
pub trait DoIt {
    fn do_it(&self);
}

impl DoIt for gizmo::Gizmo {
    fn do_it(&self) {}
}

#[test]
fn test() {
    use prost::Message;

    let mut widget_factory = widget::factory::WidgetFactory::default();
    assert_eq!(0, widget_factory.encoded_len());

    widget_factory.inner = Some(widget::factory::widget_factory::Inner {});
    assert_eq!(2, widget_factory.encoded_len());

    widget_factory.root = Some(Root {});
    assert_eq!(4, widget_factory.encoded_len());

    widget_factory.root_inner = Some(root::Inner {});
    assert_eq!(6, widget_factory.encoded_len());

    widget_factory.widget = Some(widget::Widget {});
    assert_eq!(8, widget_factory.encoded_len());

    widget_factory.widget_inner = Some(widget::widget::Inner {});
    assert_eq!(10, widget_factory.encoded_len());

    widget_factory.gizmo = Some(gizmo::Gizmo {});
    assert_eq!(12, widget_factory.encoded_len());

    widget_factory.gizmo_inner = Some(gizmo::gizmo::Inner {});
    assert_eq!(14, widget_factory.encoded_len());
}
