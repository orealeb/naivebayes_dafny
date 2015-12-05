class NaiveBayes
{
  
var  innerLabelCounts : array<map<int,map<int,int>>>;
var  outerLabelCounts : map<int, int>;

constructor () modifies {this};
//ensures innerLabelCounts =map<int,int>[ ];
{
  outerLabelCounts := map[];
  innerLabelCounts := new map<int,map<int,int>> [3];  
}  

method classify(a: array<int>)  returns (klass : int ) 
requires a!= null;
requires innerLabelCounts != null;
requires a.Length == innerLabelCounts.Length;
modifies innerLabelCounts;  
//ensures in input array
{
  var index := 0;  
  var utilLabels := new int[2];   
  var curLabel := 0;
  var labels := map[];
  while (index < |outerLabelCounts|) {    
            var attributeCounts := map[];
            var numVal := map[];
            var labe := index;
            if(index in outerLabelCounts){ 
            var countOfLabel := outerLabelCounts[index];   
            } 
            var prob := 1;      

            // start from attributes, index 1
            var i := 0;
            while (i < a.Length) 
            // invariant (a.Length > 0 ) ==> forall i :: 0 <= i < index ==> a[i] in  m;   
            {
                attributeCounts   := innerLabelCounts[i];  
                //numVal  := attributeCounts[obj[i]];  
                var countOfValueLabel := 0;
                var   totalSumOfLabel := countOfValueLabel;  

                if (a[i] in attributeCounts && labe in numVal){//(numVal != null) && numVal.containsKey(label)) {
                    countOfValueLabel := numVal[labe];   
                } else {
                    countOfValueLabel := 1;
                    totalSumOfLabel := totalSumOfLabel + 1;
                }  
                if(totalSumOfLabel != 0){
                prob := prob * (countOfValueLabel / totalSumOfLabel);
                }
                i := i + 1;
            }
            if(index in outerLabelCounts && labe in labels ){
            labels := labels[labe := prob * outerLabelCounts[index]];
            }  
            if(curLabel < utilLabels.Length){  
            utilLabels[curLabel] := labe;
            }
            curLabel := curLabel + 1;  
            index := index + 1;  
        }

        if(utilLabels[0] in labels && utilLabels[1] in labels){
        if (labels[utilLabels[0]] > labels[utilLabels[1]]) {
            return utilLabels[0];
        }  
        else{
        return utilLabels[1];
        }
        }  
       
  
}


method train(a: array2<int>)  returns () 
requires a != null;  
requires innerLabelCounts != null;  
requires innerLabelCounts.Length > 0;
requires a.Length0 > 0;       
requires a.Length1 > 0; 
requires innerLabelCounts.Length == a.Length1;
modifies innerLabelCounts;
modifies outerLabelCounts;
ensures (a.Length0 > 0 && a.Length1 > 0 ) ==> innerLabelCounts.Length > 0;
//ensures (a.Length0 > 0 && a.Length1 > 0 ) ==> (forall i : int :: i >=0 && i < a.Length0 ==> (a[i,0]  in m)); 
{  
  
  outerLabelCounts  := getCountForEachLabel(a);

 //m := map[];   
 var rowIndex := 0;
 //var innerLabelIndex := 0;  
 while (rowIndex < a.Length0 ) 
 invariant 0 <= rowIndex <= a.Length0;    
// invariant (a.Length1 > 0 && a.Length0 > 0) ==> forall i :: 0 <= i < index ==> a[i,0] in  m;   
  {  
    var columnIndex := 1; //attributes start from index 1
    while(columnIndex < a.Length1)
    invariant 0 <= rowIndex <= a.Length0 && 1 <= columnIndex <= a.Length1;
    {
      var labelCountsForValue := map[];
      //var  labelCountsForValue := new map<int,map<int,int>>;
      var value := a[rowIndex,columnIndex];

      if(rowIndex ==0)   
      {
        innerLabelCounts[columnIndex] := (labelCountsForValue);
      }
    labelCountsForValue :=     innerLabelCounts[columnIndex-1];           
           
          // labelCounts :=  labelCountsForValue[value];
          var labelCounts := map[];
          if (value !in labelCountsForValue) {                   
                    labelCountsForValue := labelCountsForValue[value := labelCounts];
          }
          else
          {
            labelCounts :=  labelCountsForValue[value];
          }

          if (a[rowIndex,0] !in labelCounts) {
                    labelCounts := labelCounts[a[rowIndex, 0] :=  1];
          } else {
                    labelCounts := labelCounts[a[rowIndex, 0] := labelCounts[a[rowIndex, 0]] + 1];
           }
                
        columnIndex := columnIndex + 1; 
    } 
    rowIndex := rowIndex + 1; 
  }
} 
 
method getCountForEachLabel(a: array2<int>)  returns (m: map<int,int>) 
requires a != null;
requires a.Length0 > 0;
requires a.Length1 > 0;
ensures (a.Length0 > 0 && a.Length1 > 0 ) ==> (forall i : int :: i >=0 && i < a.Length0 ==> (a[i,0]  in m)); 
{
 m := map[]; 
 var index := 0;
 while (index < a.Length0 ) 
 invariant 0 <= index <= a.Length0; 
 invariant (a.Length1 > 0 && a.Length0 > 0) ==> forall i :: 0 <= i < index ==> a[i,0] in  m;   
  {      
    if a[index,0] in m {   // check if count is in domain of map
      var val := m[a[index,0]];
      m := m[a[index,0] := (val + 1)];  // read result in map
    } else {
      m := m[a[index,0] := 1];  // update the map
    }   
    index := index + 1; 
  }  
  
  
}

}

method Main(){
  var trainData := new int[3,3];
  trainData[0,0] := 0;
  trainData[0,1] := 0;
  trainData[0,2] := 0;
  trainData[1,0] := 0;
  trainData[1,1] := 0;
  trainData[1,2] := 0;
  trainData[2,0] := 0;
  trainData[2,1] := 0;
  trainData[2,2] := 0;
  var nb := new NaiveBayes();
  nb.train(trainData);
}






