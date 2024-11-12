
pub fn tm<
    'a: 'b,
    'b,
    A: std::ops::DerefMut<Target = crate::Module<'a>>,
    B: std::ops::Deref<Target = crate::Module<'b>> + std::ops::DerefMut,
    S: std::ops::Deref<Target = crate::copying::module::State<I>> + std::ops::DerefMut,
    I: std::ops::Deref<Target = J> + std::ops::DerefMut,
    J: crate::copying::module::Imports + ?Sized,
>(
    p1m: &str,
    p1n: &str,
    p2: &mut crate::ImportKind,
    p3: &mut crate::copying::module::Copier<A, B, S>,
) -> anyhow::Result<()> {
    
    Ok(())
}
#[derive(Default)]
pub struct TM {}
impl TM {}
