standard library package Transfers {
    doc
    /*
     * This package defines the transfer interactions used to type flows.
     */

    private import Base::Anything;
    private import Occurrences::*;
    private import Links::*;
    private import Objects::BinaryLinkObject;
    private import Performances::Performance;
    private import Performances::performances;
    private import ScalarValues::Boolean;
    private import ScalarValues::Natural;
    private import SequenceFunctions::*;
//SFS:
     private import ScalarValues::NumericalValue;
     private import Triggers::TriggerAfter;
     private import Domain::GetChangeToFalse;
    private import Performances::BooleanEvaluation;
   
    
    interaction Transfer specializes Performance, BinaryLink {
        doc
        /*
         * A Transfer represents the transfer of a payload from the source of the interaction 
         * to the target of the interaction.
         */
    
        end feature source: Occurrence redefines BinaryLink::source {
            doc
            /*
             * The entity whose output is the source of the payload to be transferred.
             */
//SFS:  replace sourceOutput with Occurrence.outgoingBuffer        
//            feature sourceOutput: Anything[0..*];
        }
        
        end feature target: Occurrence redefines BinaryLink::target {
            doc
            /*
             * The entity whose input is the target of the payload to be transferred.
             */
//SFS:  replace targetInput with Occurrence.incomingBuffer        
//            feature targetInput: Anything[0..*];
        }
        
        feature isInstant: Boolean[1] {
            doc
            /*
             * If isInstance is true, then the transfer is instantaneous.
             */
        }

        feature transferDuration: NumericalValue[1] default 0 {
            doc
            /*
             * If isInstant is false, then transferDuration is the duration of the transfer.
             */
        }   

//SFS:  make payload multiplicity 0 for AADL event, 1 for AADL event data        
        var feature payload: Anything[0..1] {
            doc
            /*
             * The thing that is to be transferred.
             */
        }

        succession first getPayloadFromSource then delay;
        succession first delay then putPayloadToTarget;

//SFS:  add steps to move payload (may be empty)
        step getPayloadFromSource: source.outgoingBuffer.get {
            out payload;
        }
//SFS:  don't know how to insert delay if not isInstant
        step delay : TriggerAfter {
            in delay = transferDuration;
            in receiver = this;
        } 

        step putPayloadToTarget: target.incomingBuffer.put {
            in payload;
        }   

        // feature payloadNum: Natural [1] = size(payload);
        
        // private instantNum: Natural[1] = if isInstant? 1 else 0;
        // private binding instant[instantNum] of [0..1] startShot = [0..1] endShot {
        //     doc
        //     /*
        //      * If isInstant is true, then the start and end of the transfer happen at the same time.
        //      */
        // }
    }
    
    interaction MessageTransfer specializes Transfer {
        doc
        /*
         * A MessageTransfer is a Transfer that does not specify where the payload is picked
         * up and dropped off (see FlowTransfer). They are sent by SendPerformances and
         * accepted by AcceptPerformances.
         */
    }
     
    interaction FlowTransfer specializes Transfer disjoint from MessageTransfer {
        doc
        /*
         * A FlowTransfer is a Transfer identifying an output feature of the source from which
         * to pick up a payload and an input feature of the target to which to drop it off. They can
         * start when the payload is available at the source and move or copy it to the target.
         */
         
        feature isMove: Boolean[1] default true {
            doc
            /*
             * If isMove is true, then the entire payload leaves the source at the start
             * of the transfer.
             */
        }
        
        feature isPush: Boolean[1] default true {
            doc
            /*
             * If isPush is true, then the transfer begins when the payload is available
             * at the source.
             */
        }

//SFS:  remove payloadNum        
        connector sourceOutputLink: BinaryLinkObject[1] {
//        connector sourceOutputLink: BinaryLinkObject[payloadNum] {
            doc
            /*
             * The output of the payloads from the sourceOutput.
             */
        
            end [1] feature transferSource references source;
            end [1] feature transferPayload references payload; // subsets transferSource.sourceOutput;
//            end [payloadNum] feature transferPayload references payload subsets transferSource.sourceOutput;
        }
        
        connector targetInputLink: BinaryLinkObject[1] {
//        connector targetInputLink: BinaryLinkObject[payloadNum] {
            doc
            /*
             * The input of the payload to the targetInput.
             */
        
            end [1] feature transferTarget references target;
            end [1] feature transferPayload references payload; // subsets transferTarget.targetInput;
//            end [payloadNum] feature transferPayload references payload subsets transferTarget.targetInput;
        }
        
        // private connector sending: HappensDuring[payloadNum] from [1] startShot to [payloadNum] sourceOutputLink {
        //   doc
        //     /*
        //      * The start of the transfer happens during the output of each of the payloads from the
        //      * source. 
        //      */
        // }
        
        // private connector moving: HappensWhile[0..*] from [0..*] sourceOutputLink.endShot to [0..1] startShot {
        //     doc
        //     /*
        //      * If isMove is true, then all payloads leave the source at the start
        //      * of the transfer.
        //      */
        // }
        // private inv { isMove implies size(moving) == size(sourceOutputLink) }
        
        // private connector pushing: HappensWhile[0..*] from [0..*] sourceOutputLink.startShot to [0..1] startShot {
        //     doc
        //     /*
        //      * If isPush is true, then the transfer begins when the payloads are available
        //      * at the source.
        //      */
        // }
        // private inv { isPush implies size(pushing) == size(sourceOutputLink) }
        
        // private connector delivering: HappensWhile[payloadNum] from [payloadNum] targetInputLink.startShot to [1] endShot {
        //     doc
        //     /*
        //      * The input of each of the payloads to the target starts at the end of the transfer.
        //      */
        // }
    }
    
    interaction TransferBefore specializes Transfer, HappensBefore intersects Transfer, HappensBefore {
        doc
        /*
         * TransferBefore is a specialization of Transfer in which the source happens before
         * the transfer, which happens before the target.
         */
    
        end feature source: Occurrence redefines Transfer::source, HappensBefore::earlierOccurrence;
        end feature target: Occurrence redefines Transfer::target, HappensBefore::laterOccurrence;
        
        feature self: TransferBefore redefines Performance::self;
        
        private succession source then self;
        private succession self then target;
    }
    
    interaction FlowTransferBefore specializes TransferBefore, FlowTransfer intersects FlowTransfer, TransferBefore {
        doc
        /*
         * FlowTransferBefore is a FlowTransfer that is also a TransferBefore. 
         */
         
        end feature source: Occurrence redefines Transfer::source, TransferBefore::source;
        end feature target: Occurrence redefines Transfer::target, TransferBefore::target;         
    }
    
    abstract step transfers: Transfer[0..*] nonunique subsets performances, binaryLinks {
        doc
        /*
         * transfers is a specialization of performances and binaryLinks restricted to type 
         * Transfer.
         */
    
        end feature source: Occurrence redefines Transfer::source, binaryLinks::source;
        end feature target: Occurrence redefines Transfer::target, binaryLinks::target;
    }
    
    abstract step messageTransfers: MessageTransfer[0..*] nonunique subsets transfers {
        doc
        /*
         * messageTransfers is a specialization of transfers restricted to type MessageTransfers.
         */
        
        end feature source: Occurrence redefines MessageTransfer::source, transfers::source;
        end feature target: Occurrence redefines MessageTransfer::target, transfers::target;      
    }
    
    abstract flow flowTransfers: FlowTransfer[0..*] nonunique subsets transfers {
        doc
        /*
         * flowTransfers is a specialization of transfers restricted to type FlowTransfers.
         * It is the default subsetting for non-succession flows.
         */
         
        end feature source: Occurrence redefines FlowTransfer::source, transfers::source;
        end feature target: Occurrence redefines FlowTransfer::target, transfers::target;
    }
      
    abstract flow transfersBefore: TransferBefore[0..*] nonunique subsets transfers, happensBeforeLinks
        intersects transfers, happensBeforeLinks {
        doc
        /*
         * transfersBefore is a specialization of transfers and happensBeforeLinks restricted to
         * type TransferBefore.
         */
    
        end feature source: Occurrence redefines TransferBefore::source, transfers::source, happensBeforeLinks::earlierOccurrence;
        end feature target: Occurrence redefines TransferBefore::target, transfers::target, happensBeforeLinks::laterOccurrence;
    }
    
    abstract flow flowTransfersBefore: FlowTransferBefore[0..*] nonunique subsets flowTransfers, transfersBefore
        intersects flowTransfers, transfersBefore {
        doc
        /*
         * flowTransfersBefore is a specialization of flowTransfers and transfersBefore that is restricted
         * to type FlowTransferBefore. IT is the default subsetting for succession flows.
         */
    
        end feature source: Occurrence redefines FlowTransferBefore::source, flowTransfers::source, transfersBefore::source;
        end feature target: Occurrence redefines FlowTransferBefore::target, flowTransfers::target, transfersBefore::target;
    }

//SFS:  new
    behavior SendPerformance specializes Performance  {
        doc
        /*
         * SendPerformances are Performance that load a payload into the sender's outgoingBuffer
         * then move it to the receiver with a MessageTransfer.
         */
    
        in feature payload[0..1];  //changed from [0..*]
        in feature sender: Occurrence[1] default this;
        in feature receiver: Occurrence[1];

        succession loadOutgoingBuffer then sendTransfer;

        step loadOutgoingBuffer : sender.outgoingBuffer.put {
            in value = payload;
        }
        
        step sendTransfer: MessageTransfer [1] {
            feature redefines payload = SendPerformance::payload;
            end feature redefines source = sender;
            end feature redefines target = receiver;
        }

    }

    // behavior SendPerformance specializes Performance  {
    //     doc
    //     /*
    //      * SendPerformances are Performance that require an outgoingTransferFromSelf 
    //      * from a designated sender Occurrence carrying a given payload, optionally to a designated receiver.
    //      */
    //     in feature payload [0..*];
    //     in feature sender: Occurrence[1] default this;
    //     in feature receiver: Occurrence[0..1];
    //     feature sentTransfer: MessageTransfer [1] subsets sender.outgoingTransfersFromSelf {
    //         feature redefines payload = SendPerformance::payload;
    //     }
    //     binding [0..1] receiver.incomingTransfersToSelf = [1] sentTransfer;
    //     succession self then sentTransfer;
    // }
    
    behavior AcceptPerformance specializes Performance {
        doc
        /*
         * A transfer automatically puts the payload in the target's incomingBuffer
         * so AcceptPerformance waits for something in the receiver's incomingBuffer.
         */
        inout feature payload[0..1];  //changed from [0..*]
        in feature receiver: Occurrence[1] default this;

        succession first waitForTransfer then getPayloadFromBuffer;

        step waitForTransfer : GetChangeToFalse {
            in feature d = receiver {
                feature :>> e : BooleanEvaluation[1] {
                    out feature redefines result = receiver.incomingBuffer.isEmpty();
                }
            }
        }
       
        step getPayloadFromBuffer : receiver.incomingBuffer.get  {
            out feature :>> value = payload;
        }
    }
    
    // behavior AcceptPerformance specializes Performance {
    //     doc
    //     /*
    //      * AcceptPerformance is a performance that requires an incomingTransferToSelf
    //      * of a desigated receiver Occurrence, providing its payload as output.
    //      */
    //     inout feature payload[0..*];
    //     in feature receiver: Occurrence[1] default this;
    //     feature acceptedTransfer: MessageTransfer[1] subsets receiver.incomingTransfersToSelf;
    //     succession acceptedTransfer then self.endShot;
    //     binding payload = acceptedTransfer.payload;
    // }

    abstract step sendPerformances: SendPerformance[0..*] nonunique subsets performances {
        doc
        /*
         * sendPerformances is a specialization of performances for SendPerformances.
         */
    }
        
    abstract step acceptPerformances: AcceptPerformance[0..*] nonunique subsets performances {
        doc
        /*
         * acceptPerformances is a specialization of performances for AcceptPerformances.
         */
    }
}