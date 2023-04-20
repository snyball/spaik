use std::fmt;

use crate::fmt::{LispFmt, VisitSet};

impl LispFmt for glam::Vec2 {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(vec2 {} {})", self.x, self.y)
    }
}

impl LispFmt for glam::Vec3 {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(vec3 {} {} {})", self.x, self.y, self.z)
    }
}

impl LispFmt for glam::Vec4 {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(vec4 {} {} {} {})", self.x, self.y, self.z, self.w)
    }
}

impl LispFmt for glam::Mat2 {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let col0 = self.col(0);
        let col1 = self.col(1);
        write!(f, "(mat2 ({} {}) ({} {}))", col0.x, col0.y, col1.x, col1.y)
    }
}

impl LispFmt for glam::Mat3 {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let col0 = self.col(0);
        let col1 = self.col(1);
        let col2 = self.col(2);
        write!(f, "(mat3 ({} {} {}) ({} {} {}) ({} {} {}))",
               col0.x, col0.y, col0.z,
               col1.x, col1.y, col1.z,
               col2.x, col2.y, col2.z)
    }
}
impl LispFmt for glam::Mat4 {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        let col0 = self.col(0);
        let col1 = self.col(1);
        let col2 = self.col(2);
        let col3 = self.col(3);
        write!(f, "(mat4 ({} {} {} {}) ({} {} {} {}) ({} {} {} {}) ({} {} {} {}))",
               col0.x, col0.y, col0.z, col0.w,
               col1.x, col1.y, col1.z, col1.w,
               col2.x, col2.y, col2.z, col2.w,
               col3.x, col3.y, col3.z, col3.w)
    }
}

impl LispFmt for glam::Quat {
    fn lisp_fmt(&self,
                _visited: &mut VisitSet,
                f: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(f, "(quat {} {} {} {})", self.x, self.y, self.z, self.w)
    }
}
