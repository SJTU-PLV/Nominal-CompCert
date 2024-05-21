fn test<'c, 'a: 'c, 'b>(a: &'a mut i32, b: &'b mut i32) -> &'c mut i32{
    return &mut *a
}