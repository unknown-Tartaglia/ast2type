import { contentAll } from '../../../utils/util';
export default {
  clickItem(actionCode, gotoURL, index) {
    const pageId = this.props?.pageId;
    const res = contentAll(actionCode, pageId, gotoURL, index);
    return res;
  },
};
