
open OUnitTest
open TestCommon
open OUnit2

let test_case = TestCase (fun ctxt -> ())
let labeled_test_case = TestLabel ("label", test_case)
let suite_a = TestLabel ("suite_a", TestList [test_case])
let suite_b = TestLabel ("suite_b", TestList [labeled_test_case])
let suite_c = TestLabel ("suite_c", TestList [test_case; labeled_test_case])
let suite_d = TestLabel ("suite_d", TestList [suite_a; suite_c])

let rec string_of_paths = function
    [] -> ""
  | h::t -> (string_of_path h) ^ "\n" ^ (string_of_paths t)

let test_case_filter ctxt =
  let assert_test_case_count exp tst_opt =
    match tst_opt with
      | Some tst ->
          assert_equal exp (test_case_count tst)
      | None ->
          assert_failure "Unexpected empty filter result"
  in
  assert_equal None (test_filter [] suite_a);
  assert_equal None (test_filter [] suite_b);
  assert_equal None (test_filter [] suite_c);
  assert_equal None (test_filter [] suite_d);
  assert_test_case_count 1 (test_filter ["suite_a"] suite_a);
  assert_test_case_count 1 (test_filter ["suite_a:0"] suite_a);
  assert_test_case_count 1 (test_filter ["suite_b:0:label"] suite_b);
  assert_test_case_count 1 (test_filter ["suite_c:0"] suite_c);
  assert_test_case_count 2 (test_filter ["suite_c:0";"suite_c:1:label"]
                              suite_c)

let test_case_decorate ctxt =
    assert_equal_test_result
      [
        [Label "label"; ListItem 1; Label "suite_c"],
        RSuccess,
        None;

        [ListItem 0; Label "suite_c"],
        RSuccess,
        None
      ]
      (perform_test suite_c);
    assert_equal_test_result
      [
        [Label "label"; ListItem 1; Label "suite_c"],
        RFailure("OUnit: fail", None),
        None;

        [ListItem 0; Label "suite_c"],
        RFailure("OUnit: fail", None),
        None;
      ]
      (perform_test
         (test_decorate
            (fun _ -> (fun ctxt -> assert_failure "fail"))
            suite_c))

(* Test which checks if the test case count function works correctly *)
let test_case_count ctxt =
  let assert_equal ?msg = assert_equal ?msg ~printer:string_of_int in
  assert_equal 0 (test_case_count (TestList []));
  assert_equal 0 (test_case_count (TestLabel("label", TestList [])));
  assert_equal 0
    (test_case_count
       (TestList [TestList [];
                  TestList [TestList []]]));

  assert_equal 1 (test_case_count test_case);
  assert_equal 1 (test_case_count labeled_test_case);
  assert_equal 1 (test_case_count suite_a);
  assert_equal 1 (test_case_count suite_b);

  assert_equal 1 (test_case_count (TestList [suite_a; TestList []]));
  assert_equal 1
    (test_case_count
       (TestList [TestList [];
                  TestList [suite_b]]));
  assert_equal 2 (test_case_count suite_c);
  assert_equal 3 (test_case_count suite_d)

(* Test which checks if the paths are correctly constructed *)
let test_case_paths _ =
      (* A single testcase results in a list countaining an empty list *)
  let assert_equal ?msg = assert_equal ?msg ~printer:string_of_paths in
  assert_equal [[]] (test_case_paths test_case);
  assert_equal [[Label "label"]]
    (test_case_paths labeled_test_case);
  assert_equal [[ListItem 0; Label "suite_a"]]
    (test_case_paths suite_a);
  assert_equal [[Label "label"; ListItem 0; Label "suite_b"]]
    (test_case_paths suite_b);
  assert_equal [[ListItem 0; Label "suite_c"];
                [Label "label"; ListItem 1; Label "suite_c"]]
    (test_case_paths suite_c);
  assert_equal [[ListItem 0; Label "suite_a"; ListItem 0; Label "suite_d"];
                [ListItem 0; Label "suite_c"; ListItem 1; Label "suite_d"];
                [Label "label"; ListItem 1; Label "suite_c"; ListItem 1;
                 Label "suite_d"]]
    (test_case_paths suite_d)

let tests =
  "OUnitTest" >:::
  [ "test_case_count" >:: test_case_count;
    "test_case_paths" >:: test_case_paths;
    "test_case_filter" >:: test_case_filter;
    "test_case_decorate" >:: test_case_decorate;
  ]

